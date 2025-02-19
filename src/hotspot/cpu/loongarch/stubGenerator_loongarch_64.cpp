/*
 * Copyright (c) 2003, 2013, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2015, 2025, Loongson Technology. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "precompiled.hpp"
#include "asm/macroAssembler.hpp"
#include "asm/macroAssembler.inline.hpp"
#include "compiler/oopMap.hpp"
#include "gc/shared/barrierSet.hpp"
#include "gc/shared/barrierSetAssembler.hpp"
#include "interpreter/interpreter.hpp"
#include "nativeInst_loongarch.hpp"
#include "oops/instanceOop.hpp"
#include "oops/method.hpp"
#include "oops/objArrayKlass.hpp"
#include "oops/oop.inline.hpp"
#include "prims/methodHandles.hpp"
#include "prims/upcallLinker.hpp"
#include "runtime/continuation.hpp"
#include "runtime/continuationEntry.inline.hpp"
#include "runtime/frame.inline.hpp"
#include "runtime/handles.inline.hpp"
#include "runtime/javaThread.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/stubCodeGenerator.hpp"
#include "runtime/stubRoutines.hpp"
#include "utilities/copy.hpp"

#ifdef COMPILER2
#include "opto/runtime.hpp"
#endif
#if INCLUDE_JFR
#include "jfr/support/jfrIntrinsics.hpp"
#endif
#if INCLUDE_ZGC
#include "gc/z/zBarrierSetAssembler.hpp"
#endif

#if INCLUDE_ZGC
#include "gc/z/zThreadLocalData.hpp"
#endif

// Declaration and definition of StubGenerator (no .hpp file).
// For a more detailed description of the stub routine structure
// see the comment in stubRoutines.hpp

#define __ _masm->

#ifdef PRODUCT
#define BLOCK_COMMENT(str) /* nothing */
#else
#define BLOCK_COMMENT(str) __ block_comment(str)
#endif

#define BIND(label) bind(label); BLOCK_COMMENT(#label ":")

// Stub Code definitions

class StubGenerator: public StubCodeGenerator {
 private:

  // Call stubs are used to call Java from C
  //
  // Arguments:
  //    c_rarg0:   call wrapper address                   address
  //    c_rarg1:   result                                 address
  //    c_rarg2:   result type                            BasicType
  //    c_rarg3:   method                                 Method*
  //    c_rarg4:   (interpreter) entry point              address
  //    c_rarg5:   parameters                             intptr_t*
  //    c_rarg6:   parameter size (in words)              int
  //    c_rarg7:   thread                                 Thread*
  //
  // we don't need to save all arguments, since both C and Java treat
  // them as volatile registers.
  //
  // we only need to keep call wrapper address (c_rarg0) for Java frame,
  // and restore the stub result via c_rarg1 and c_rarg2.
  //
  // we save RA as the return PC at the base of the frame and link FP
  // below it as the frame pointer.
  //
  // we save S0-S8 and F24-F31 which are expected to be callee-saved.
  //
  // so the stub frame looks like this when we enter Java code
  //
  //     [ return_from_Java     ] <--- sp
  //     [ argument word n      ]
  //      ...
  // -23 [ argument word 1      ]
  // -22 [ F31                  ] <--- sp_after_call
  //      ...
  // -15 [ F24                  ]
  // -14 [ S8                   ]
  //      ...
  //  -6 [ S0                   ]
  //  -5 [ result_type          ] <--- c_rarg2
  //  -4 [ result               ] <--- c_rarg1
  //  -3 [ call wrapper         ] <--- c_rarg0
  //  -2 [ saved FP             ]
  //  -1 [ saved RA             ]
  //   0 [                      ] <--- fp

  // Call stub stack layout word offsets from fp
  enum call_stub_layout {
    sp_after_call_off  = -22,

    F31_off            = -22,
    F30_off            = -21,
    F29_off            = -20,
    F28_off            = -19,
    F27_off            = -18,
    F26_off            = -17,
    F25_off            = -16,
    F24_off            = -15,

    S8_off             = -14,
    S7_off             = -13,
    S6_off             = -12,
    S5_off             = -11,
    S4_off             = -10,
    S3_off             = -9,
    S2_off             = -8,
    S1_off             = -7,
    S0_off             = -6,

    result_type_off    = -5,
    result_off         = -4,
    call_wrapper_off   = -3,
    FP_off             = -2,
    RA_off             = -1,
  };

  address generate_call_stub(address& return_address) {
    assert((int)frame::entry_frame_after_call_words == -(int)sp_after_call_off + 1 &&
           (int)frame::entry_frame_call_wrapper_offset == (int)call_wrapper_off,
           "adjust this code");

    StubCodeMark mark(this, "StubRoutines", "call_stub");

    // stub code

    address start = __ pc();

    // set up frame and move sp to end of save area
    __ enter();
    __ addi_d(SP, FP, sp_after_call_off * wordSize);

    // save register parameters and Java temporary/global registers
    __ st_d(A0, FP, call_wrapper_off * wordSize);
    __ st_d(A1, FP, result_off * wordSize);
    __ st_d(A2, FP, result_type_off * wordSize);

    __ st_d(S0, FP, S0_off * wordSize);
    __ st_d(S1, FP, S1_off * wordSize);
    __ st_d(S2, FP, S2_off * wordSize);
    __ st_d(S3, FP, S3_off * wordSize);
    __ st_d(S4, FP, S4_off * wordSize);
    __ st_d(S5, FP, S5_off * wordSize);
    __ st_d(S6, FP, S6_off * wordSize);
    __ st_d(S7, FP, S7_off * wordSize);
    __ st_d(S8, FP, S8_off * wordSize);

    __ fst_d(F24, FP, F24_off * wordSize);
    __ fst_d(F25, FP, F25_off * wordSize);
    __ fst_d(F26, FP, F26_off * wordSize);
    __ fst_d(F27, FP, F27_off * wordSize);
    __ fst_d(F28, FP, F28_off * wordSize);
    __ fst_d(F29, FP, F29_off * wordSize);
    __ fst_d(F30, FP, F30_off * wordSize);
    __ fst_d(F31, FP, F31_off * wordSize);

    // install Java thread in global register now we have saved
    // whatever value it held
    __ move(TREG, A7);

    // init Method*
    __ move(Rmethod, A3);

    // set up the heapbase register
    __ reinit_heapbase();

#ifdef ASSERT
    // make sure we have no pending exceptions
    {
      Label L;
      __ ld_d(AT, TREG, in_bytes(Thread::pending_exception_offset()));
      __ beqz(AT, L);
      __ stop("StubRoutines::call_stub: entered with pending exception");
      __ bind(L);
    }
#endif

    // pass parameters if any
    // c_rarg5: parameter_pointer
    // c_rarg6: parameter_size
    Label parameters_done;
    __ beqz(c_rarg6, parameters_done);

    __ slli_d(c_rarg6, c_rarg6, LogBytesPerWord);
    __ sub_d(SP, SP, c_rarg6);
    assert(StackAlignmentInBytes == 16, "must be");
    __ bstrins_d(SP, R0, 3, 0);

    address loop = __ pc();
    __ ld_d(AT, c_rarg5, 0);
    __ addi_d(c_rarg5, c_rarg5, wordSize);
    __ addi_d(c_rarg6, c_rarg6, -wordSize);
    __ stx_d(AT, SP, c_rarg6);
    __ blt(R0, c_rarg6, loop);

    __ bind(parameters_done);

    // call Java entry -- passing methdoOop, and current sp
    //      Rmethod: Method*
    //      Rsender: sender sp
    BLOCK_COMMENT("call Java function");
    __ move(Rsender, SP);
    __ jalr(c_rarg4);

    // save current address for use by exception handling code

    return_address = __ pc();

    // store result depending on type (everything that is not
    // T_OBJECT, T_LONG, T_FLOAT or T_DOUBLE is treated as T_INT)
    // n.b. this assumes Java returns an integral result in A0
    // and a floating result in FA0
    __ ld_d(c_rarg1, FP, result_off * wordSize);
    __ ld_d(c_rarg2, FP, result_type_off * wordSize);

    Label is_long, is_float, is_double, exit;

    __ addi_d(AT, c_rarg2, (-1) * T_OBJECT);
    __ beqz(AT, is_long);
    __ addi_d(AT, c_rarg2, (-1) * T_LONG);
    __ beqz(AT, is_long);
    __ addi_d(AT, c_rarg2, (-1) * T_FLOAT);
    __ beqz(AT, is_float);
    __ addi_d(AT, c_rarg2, (-1) * T_DOUBLE);
    __ beqz(AT, is_double);

    // handle T_INT case
    __ st_w(A0, c_rarg1, 0);

    __ bind(exit);

    __ pop_cont_fastpath(TREG);

    // restore callee-save registers

    __ ld_d(S0, FP, S0_off * wordSize);
    __ ld_d(S1, FP, S1_off * wordSize);
    __ ld_d(S2, FP, S2_off * wordSize);
    __ ld_d(S3, FP, S3_off * wordSize);
    __ ld_d(S4, FP, S4_off * wordSize);
    __ ld_d(S5, FP, S5_off * wordSize);
    __ ld_d(S6, FP, S6_off * wordSize);
    __ ld_d(S7, FP, S7_off * wordSize);
    __ ld_d(S8, FP, S8_off * wordSize);

    __ fld_d(F24, FP, F24_off * wordSize);
    __ fld_d(F25, FP, F25_off * wordSize);
    __ fld_d(F26, FP, F26_off * wordSize);
    __ fld_d(F27, FP, F27_off * wordSize);
    __ fld_d(F28, FP, F28_off * wordSize);
    __ fld_d(F29, FP, F29_off * wordSize);
    __ fld_d(F30, FP, F30_off * wordSize);
    __ fld_d(F31, FP, F31_off * wordSize);

    // leave frame and return to caller
    __ leave();
    __ jr(RA);

    // handle return types different from T_INT
    __ bind(is_long);
    __ st_d(A0, c_rarg1, 0);
    __ b(exit);

    __ bind(is_float);
    __ fst_s(FA0, c_rarg1, 0);
    __ b(exit);

    __ bind(is_double);
    __ fst_d(FA0, c_rarg1, 0);
    __ b(exit);

    return start;
  }

  // Return point for a Java call if there's an exception thrown in
  // Java code.  The exception is caught and transformed into a
  // pending exception stored in JavaThread that can be tested from
  // within the VM.
  //
  // Note: Usually the parameters are removed by the callee. In case
  // of an exception crossing an activation frame boundary, that is
  // not the case if the callee is compiled code => need to setup the
  // sp.
  //
  // V0: exception oop

  address generate_catch_exception() {
    StubCodeMark mark(this, "StubRoutines", "catch_exception");
    address start = __ pc();

#ifdef ASSERT
    // verify that threads correspond
    { Label L;
      __ get_thread(T8);
      __ beq(T8, TREG, L);
      __ stop("StubRoutines::catch_exception: threads must correspond");
      __ bind(L);
    }
#endif
    // set pending exception
    __ verify_oop(V0);
    __ st_d(V0, TREG, in_bytes(Thread::pending_exception_offset()));
    __ li(AT, (long)__FILE__);
    __ st_d(AT, TREG, in_bytes(Thread::exception_file_offset   ()));
    __ li(AT, (long)__LINE__);
    __ st_d(AT, TREG, in_bytes(Thread::exception_line_offset   ()));

    // complete return to VM
    assert(StubRoutines::_call_stub_return_address != nullptr, "_call_stub_return_address must have been generated before");
    __ jmp(StubRoutines::_call_stub_return_address, relocInfo::none);
    return start;
  }

  // Continuation point for runtime calls returning with a pending
  // exception.  The pending exception check happened in the runtime
  // or native call stub.  The pending exception in Thread is
  // converted into a Java-level exception.
  //
  // Contract with Java-level exception handlers:
  //   A0: exception
  //   A1: throwing pc
  //
  // NOTE: At entry of this stub, exception-pc must be in RA !!

  address generate_forward_exception() {
    StubCodeMark mark(this, "StubRoutines", "forward exception");
    address start = __ pc();

    // Upon entry, RA points to the return address returning into
    // Java (interpreted or compiled) code; i.e., the return address
    // becomes the throwing pc.
    //
    // Arguments pushed before the runtime call are still on the stack
    // but the exception handler will reset the stack pointer ->
    // ignore them.  A potential result in registers can be ignored as
    // well.

#ifdef ASSERT
    // make sure this code is only executed if there is a pending exception
    {
      Label L;
      __ ld_d(AT, Address(TREG, Thread::pending_exception_offset()));
      __ bnez(AT, L);
      __ stop("StubRoutines::forward exception: no pending exception (1)");
      __ bind(L);
    }
#endif

    const Register exception_handler = T4;

    __ move(TSR, RA); // keep return address in callee-saved register
    __ call_VM_leaf(
         CAST_FROM_FN_PTR(address, SharedRuntime::exception_handler_for_return_address),
         TREG, RA);
    __ move(RA, TSR); // restore

    __ move(exception_handler, A0);
    __ move(A1, RA); // save throwing pc

    __ ld_d(A0, TREG, in_bytes(Thread::pending_exception_offset()));
    __ st_d(R0, TREG, in_bytes(Thread::pending_exception_offset()));

#ifdef ASSERT
    // make sure exception is set
    {
      Label L;
      __ bnez(A0, L);
      __ stop("StubRoutines::forward exception: no pending exception (2)");
      __ bind(L);
    }
#endif

    // continue at exception handler (return address removed)
    //   A0: exception
    //   A1: throwing pc
    __ verify_oop(A0);
    __ jr(exception_handler);

    return start;
  }

  // Non-destructive plausibility checks for oops
  //
  // Arguments:
  //    c_rarg0: error message
  //    c_rarg1: oop to verify
  //
  // Stack after saving c_rarg3:
  //    [tos + 0]: saved c_rarg3
  //    [tos + 1]: saved c_rarg2
  //    [tos + 2]: saved c_rarg1
  //    [tos + 3]: saved c_rarg0
  //    [tos + 4]: saved AT
  //    [tos + 5]: saved RA
  address generate_verify_oop() {

    StubCodeMark mark(this, "StubRoutines", "verify_oop");
    address start = __ pc();

    Label exit, error;

    const Register msg = c_rarg0;
    const Register oop = c_rarg1;

    __ push(RegSet::of(c_rarg2, c_rarg3));

    __ li(c_rarg2, (address) StubRoutines::verify_oop_count_addr());
    __ ld_d(c_rarg3, Address(c_rarg2));
    __ addi_d(c_rarg3, c_rarg3, 1);
    __ st_d(c_rarg3, Address(c_rarg2));

    // make sure object is 'reasonable'
    __ beqz(oop, exit); // if obj is null it is OK

    BarrierSetAssembler* bs_asm = BarrierSet::barrier_set()->barrier_set_assembler();
    bs_asm->check_oop(_masm, oop, c_rarg2, c_rarg3, error);

    // return if everything seems ok
    __ bind(exit);
    __ pop(RegSet::of(c_rarg2, c_rarg3));
    __ jr(RA);

    // handle errors
    __ bind(error);
    __ pop(RegSet::of(c_rarg2, c_rarg3));
    // error message already in c_rarg0, pass it to debug
    __ call(CAST_FROM_FN_PTR(address, MacroAssembler::debug), relocInfo::runtime_call_type);
    __ brk(5);

    return start;
  }

  // Generate indices for iota vector.
  address generate_iota_indices(const char *stub_name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", stub_name);
    address start = __ pc();
    // B
    __ emit_data64(0x0706050403020100, relocInfo::none);
    __ emit_data64(0x0F0E0D0C0B0A0908, relocInfo::none);
    __ emit_data64(0x1716151413121110, relocInfo::none);
    __ emit_data64(0x1F1E1D1C1B1A1918, relocInfo::none);
    // H
    __ emit_data64(0x0003000200010000, relocInfo::none);
    __ emit_data64(0x0007000600050004, relocInfo::none);
    __ emit_data64(0x000B000A00090008, relocInfo::none);
    __ emit_data64(0x000F000E000D000C, relocInfo::none);
    // W
    __ emit_data64(0x0000000100000000, relocInfo::none);
    __ emit_data64(0x0000000300000002, relocInfo::none);
    __ emit_data64(0x0000000500000004, relocInfo::none);
    __ emit_data64(0x0000000700000006, relocInfo::none);
    // D
    __ emit_data64(0x0000000000000000, relocInfo::none);
    __ emit_data64(0x0000000000000001, relocInfo::none);
    __ emit_data64(0x0000000000000002, relocInfo::none);
    __ emit_data64(0x0000000000000003, relocInfo::none);
    // S - FP
    __ emit_data64(0x3F80000000000000, relocInfo::none); // 0.0f, 1.0f
    __ emit_data64(0x4040000040000000, relocInfo::none); // 2.0f, 3.0f
    __ emit_data64(0x40A0000040800000, relocInfo::none); // 4.0f, 5.0f
    __ emit_data64(0x40E0000040C00000, relocInfo::none); // 6.0f, 7.0f
    // D - FP
    __ emit_data64(0x0000000000000000, relocInfo::none); // 0.0d
    __ emit_data64(0x3FF0000000000000, relocInfo::none); // 1.0d
    __ emit_data64(0x4000000000000000, relocInfo::none); // 2.0d
    __ emit_data64(0x4008000000000000, relocInfo::none); // 3.0d
    return start;
  }

  //
  // Generate stub for array fill. If "aligned" is true, the
  // "to" address is assumed to be heapword aligned.
  //
  // Arguments for generated stub:
  //   to:    A0
  //   value: A1
  //   count: A2 treated as signed
  //
  address generate_fill(BasicType t, bool aligned, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    const Register to        = A0;  // source array address
    const Register value     = A1;  // value
    const Register count     = A2;  // elements count

    if (UseLASX) {
      __ array_fill_lasx(t, to, value, count);
    } else if (UseLSX) {
      __ array_fill_lsx(t, to, value, count);
    } else {
      __ array_fill(t, to, value, count, aligned);
    }

    return start;
  }

  //
  //  Generate overlap test for array copy stubs
  //
  //  Input:
  //    A0   - source array address
  //    A1   - destination array address
  //    A2   - element count
  //
  //  Temp:
  //    AT   - destination array address - source array address
  //    T4   - element count * element size
  //
  void array_overlap_test(address no_overlap_target, int log2_elem_size) {
    __ slli_d(T4, A2, log2_elem_size);
    __ sub_d(AT, A1, A0);
    __ bgeu(AT, T4, no_overlap_target);
  }

  // disjoint large copy
  void generate_disjoint_large_copy(DecoratorSet decorators, BasicType type, Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Register gct1 = S0;
    Register gct2 = S1;
    Register gct3 = S2;
    BarrierSetAssembler* bs = BarrierSet::barrier_set()->barrier_set_assembler();

    {
      UnsafeMemoryAccessMark umam(this, true, true);
      Label loop, le32, le16, le8, lt8;

      __ bind(entry);
#if INCLUDE_ZGC
      if (UseZGC && is_reference_type(type)) {
        __ push(RegSet::of(gct1, gct2, gct3));
      }
#endif
      __ add_d(A3, A1, A2);
      __ add_d(A2, A0, A2);
      bs->copy_load_at(_masm, decorators, type, 8, A6, Address(A0, 0), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, A7, Address(A2, -8), gct1);

      __ andi(T1, A1, 7);
      __ sub_d(T0, R0, T1);
      __ addi_d(T0, T0, 8);

      __ add_d(A0, A0, T0);
      __ add_d(A5, A1, T0);

      __ addi_d(A4, A2, -64);
      __ bgeu(A0, A4, le32);

      __ bind(loop);
      bs->copy_load_at(_masm, decorators, type, 8, T0, Address(A0, 0),  gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T1, Address(A0, 8),  gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T2, Address(A0, 16), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T3, Address(A0, 24), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T4, Address(A0, 32), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T5, Address(A0, 40), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T6, Address(A0, 48), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T8, Address(A0, 56), gct1);
      __ addi_d(A0, A0, 64);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 0),  T0, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 8),  T1, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 16), T2, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 24), T3, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 32), T4, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 40), T5, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 48), T6, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 56), T8, gct1, gct2, gct3);
      __ addi_d(A5, A5, 64);
      __ bltu(A0, A4, loop);

      __ bind(le32);
      __ addi_d(A4, A2, -32);
      __ bgeu(A0, A4, le16);
      bs->copy_load_at(_masm, decorators, type, 8, T0, Address(A0, 0),  gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T1, Address(A0, 8),  gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T2, Address(A0, 16), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T3, Address(A0, 24), gct1);
      __ addi_d(A0, A0, 32);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 0),  T0, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 8),  T1, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 16), T2, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 24), T3, gct1, gct2, gct3);
      __ addi_d(A5, A5, 32);

      __ bind(le16);
      __ addi_d(A4, A2, -16);
      __ bgeu(A0, A4, le8);
      bs->copy_load_at(_masm, decorators, type, 8, T0, Address(A0, 0), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T1, Address(A0, 8), gct1);
      __ addi_d(A0, A0, 16);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 0), T0, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 8), T1, gct1, gct2, gct3);
      __ addi_d(A5, A5, 16);

      __ bind(le8);
      __ addi_d(A4, A2, -8);
      __ bgeu(A0, A4, lt8);
      bs->copy_load_at(_masm, decorators, type, 8, T0, Address(A0, 0), gct1);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, 0), T0, gct1, gct2, gct3);

      __ bind(lt8);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 0), A6, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A3, -8), A7, gct1, gct2, gct3);
#if INCLUDE_ZGC
      if (UseZGC && is_reference_type(type)) {
        __ pop(RegSet::of(gct1, gct2, gct3));
      }
#endif
    }

    __ move(A0, R0);
    __ jr(RA);
  }

  // disjoint large copy lsx
  void generate_disjoint_large_copy_lsx(DecoratorSet decorators, BasicType type, Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Register gct1 = T2;
    Register gct2 = T3;
    Register gct3 = T4;
    Register gct4 = T5;
    FloatRegister gcvt1 = FT8;
    FloatRegister gcvt2 = FT9;
    BarrierSetAssembler* bs = BarrierSet::barrier_set()->barrier_set_assembler();

    {
      UnsafeMemoryAccessMark umam(this, true, true);
      Label loop, le64, le32, le16, lt16;

      __ bind(entry);
      __ add_d(A3, A1, A2);
      __ add_d(A2, A0, A2);
      bs->copy_load_at(_masm, decorators, type, 16, F0, Address(A0, 0),   gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, F1, Address(A2, -16), gct1, gct2, gcvt1);

      __ andi(T1, A1, 15);
      __ sub_d(T0, R0, T1);
      __ addi_d(T0, T0, 16);

      __ add_d(A0, A0, T0);
      __ add_d(A5, A1, T0);

      __ addi_d(A4, A2, -128);
      __ bgeu(A0, A4, le64);

      __ bind(loop);
      bs->copy_load_at(_masm, decorators, type, 16, FT0, Address(A0, 0),   gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT1, Address(A0, 16),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT2, Address(A0, 32),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT3, Address(A0, 48),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT4, Address(A0, 64),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT5, Address(A0, 80),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT6, Address(A0, 96),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT7, Address(A0, 112), gct1, gct2, gcvt1);
      __ addi_d(A0, A0, 128);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 0),   FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 16),  FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 32),  FT2, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 48),  FT3, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 64),  FT4, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 80),  FT5, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 96),  FT6, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 112), FT7, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, 128);
      __ bltu(A0, A4, loop);

      __ bind(le64);
      __ addi_d(A4, A2, -64);
      __ bgeu(A0, A4, le32);
      bs->copy_load_at(_masm, decorators, type, 16, FT0, Address(A0, 0),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT1, Address(A0, 16), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT2, Address(A0, 32), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT3, Address(A0, 48), gct1, gct2, gcvt1);
      __ addi_d(A0, A0, 64);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 0),  FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 16), FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 32), FT2, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 48), FT3, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, 64);

      __ bind(le32);
      __ addi_d(A4, A2, -32);
      __ bgeu(A0, A4, le16);
      bs->copy_load_at(_masm, decorators, type, 16, FT0, Address(A0, 0),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT1, Address(A0, 16), gct1, gct2, gcvt1);
      __ addi_d(A0, A0, 32);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 0),  FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 16), FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, 32);

      __ bind(le16);
      __ addi_d(A4, A2, -16);
      __ bgeu(A0, A4, lt16);
      bs->copy_load_at(_masm, decorators, type, 16, FT0, Address(A0, 0), gct1, gct2, gcvt1);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, 0), FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);

      __ bind(lt16);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A1, 0),   F0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A3, -16), F1, gct1, gct2, gct3, gct4, gcvt1, gcvt2, false /* need_save_restore */);
    }

    __ move(A0, R0);
    __ jr(RA);
  }

  // disjoint large copy lasx
  void generate_disjoint_large_copy_lasx(DecoratorSet decorators, BasicType type, Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Register gct1 = T2;
    Register gct2 = T3;
    Register gct3 = T4;
    Register gct4 = T5;
    FloatRegister gcvt1 = FT8;
    FloatRegister gcvt2 = FT9;
    BarrierSetAssembler* bs = BarrierSet::barrier_set()->barrier_set_assembler();

    {
      UnsafeMemoryAccessMark umam(this, true, true);
      Label loop, le128, le64, le32, lt32;

      __ bind(entry);
      __ add_d(A3, A1, A2);
      __ add_d(A2, A0, A2);
      bs->copy_load_at(_masm, decorators, type, 32, F0, Address(A0, 0),   gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, F1, Address(A2, -32), gct1, gct2, gcvt1);

      __ andi(T1, A1, 31);
      __ sub_d(T0, R0, T1);
      __ addi_d(T0, T0, 32);

      __ add_d(A0, A0, T0);
      __ add_d(A5, A1, T0);

      __ addi_d(A4, A2, -256);
      __ bgeu(A0, A4, le128);

      __ bind(loop);
      bs->copy_load_at(_masm, decorators, type, 32, FT0, Address(A0, 0),   gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT1, Address(A0, 32),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT2, Address(A0, 64),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT3, Address(A0, 96),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT4, Address(A0, 128), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT5, Address(A0, 160), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT6, Address(A0, 192), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT7, Address(A0, 224), gct1, gct2, gcvt1);
      __ addi_d(A0, A0, 256);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 0),   FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 32),  FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 64),  FT2, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 96),  FT3, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 128), FT4, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 160), FT5, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 192), FT6, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 224), FT7, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, 256);
      __ bltu(A0, A4, loop);

      __ bind(le128);
      __ addi_d(A4, A2, -128);
      __ bgeu(A0, A4, le64);
      bs->copy_load_at(_masm, decorators, type, 32, FT0, Address(A0, 0),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT1, Address(A0, 32), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT2, Address(A0, 64), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT3, Address(A0, 96), gct1, gct2, gcvt1);
      __ addi_d(A0, A0, 128);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 0),  FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 32), FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 64), FT2, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 96), FT3, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, 128);

      __ bind(le64);
      __ addi_d(A4, A2, -64);
      __ bgeu(A0, A4, le32);
      bs->copy_load_at(_masm, decorators, type, 32, FT0, Address(A0, 0),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT1, Address(A0, 32), gct1, gct2, gcvt1);
      __ addi_d(A0, A0, 64);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 0),  FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 32), FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, 64);

      __ bind(le32);
      __ addi_d(A4, A2, -32);
      __ bgeu(A0, A4, lt32);
      bs->copy_load_at(_masm, decorators, type, 32, FT0, Address(A0, 0), gct1, gct2, gcvt1);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, 0), FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);

      __ bind(lt32);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A1, 0),   F0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A3, -32), F1, gct1, gct2, gct3, gct4, gcvt1, gcvt2, false /* need_save_restore */);
    }

    __ move(A0, R0);
    __ jr(RA);
  }

  // conjoint large copy
  void generate_conjoint_large_copy(DecoratorSet decorators, BasicType type, Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Register gct1 = S0;
    Register gct2 = S1;
    Register gct3 = S2;
    BarrierSetAssembler* bs = BarrierSet::barrier_set()->barrier_set_assembler();

    {
      UnsafeMemoryAccessMark umam(this, true, true);
      Label loop, le32, le16, le8, lt8;

      __ bind(entry);
#if INCLUDE_ZGC
      if (UseZGC && is_reference_type(type)) {
        __ push(RegSet::of(gct1, gct2, gct3));
      }
#endif
      __ add_d(A3, A1, A2);
      __ add_d(A2, A0, A2);
      bs->copy_load_at(_masm, decorators, type, 8, A6, Address(A0, 0), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, A7, Address(A2, -8), gct1);

      __ andi(T1, A3, 7);
      __ sub_d(A2, A2, T1);
      __ sub_d(A5, A3, T1);

      __ addi_d(A4, A0, 64);
      __ bgeu(A4, A2, le32);

      __ bind(loop);
      bs->copy_load_at(_masm, decorators, type, 8, T0, Address(A2, -8),  gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T1, Address(A2, -16), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T2, Address(A2, -24), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T3, Address(A2, -32), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T4, Address(A2, -40), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T5, Address(A2, -48), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T6, Address(A2, -56), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T8, Address(A2, -64), gct1);
      __ addi_d(A2, A2, -64);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -8),  T0, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -16), T1, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -24), T2, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -32), T3, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -40), T4, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -48), T5, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -56), T6, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -64), T8, gct1, gct2, gct3);
      __ addi_d(A5, A5, -64);
      __ bltu(A4, A2, loop);

      __ bind(le32);
      __ addi_d(A4, A0, 32);
      __ bgeu(A4, A2, le16);
      bs->copy_load_at(_masm, decorators, type, 8, T0, Address(A2, -8),  gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T1, Address(A2, -16), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T2, Address(A2, -24), gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T3, Address(A2, -32), gct1);
      __ addi_d(A2, A2, -32);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -8),  T0, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -16), T1, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -24), T2, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -32), T3, gct1, gct2, gct3);
      __ addi_d(A5, A5, -32);

      __ bind(le16);
      __ addi_d(A4, A0, 16);
      __ bgeu(A4, A2, le8);
      bs->copy_load_at(_masm, decorators, type, 8, T0, Address(A2, -8),  gct1);
      bs->copy_load_at(_masm, decorators, type, 8, T1, Address(A2, -16), gct1);
      __ addi_d(A2, A2, -16);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -8),  T0, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -16), T1, gct1, gct2, gct3);
      __ addi_d(A5, A5, -16);

      __ bind(le8);
      __ addi_d(A4, A0, 8);
      __ bgeu(A4, A2, lt8);
      bs->copy_load_at(_masm, decorators, type, 8, T0, Address(A2, -8), gct1);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A5, -8), T0, gct1, gct2, gct3);

      __ bind(lt8);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 0),  A6, gct1, gct2, gct3);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A3, -8), A7, gct1, gct2, gct3);
#if INCLUDE_ZGC
      if (UseZGC && is_reference_type(type)) {
        __ pop(RegSet::of(gct1, gct2, gct3));
      }
#endif
    }

    __ move(A0, R0);
    __ jr(RA);
  }

  // conjoint large copy lsx
  void generate_conjoint_large_copy_lsx(DecoratorSet decorators, BasicType type, Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Register gct1 = T2;
    Register gct2 = T3;
    Register gct3 = T4;
    Register gct4 = T5;
    FloatRegister gcvt1 = FT8;
    FloatRegister gcvt2 = FT9;
    BarrierSetAssembler* bs = BarrierSet::barrier_set()->barrier_set_assembler();

    {
      UnsafeMemoryAccessMark umam(this, true, true);
      Label loop, le64, le32, le16, lt16;

      __ bind(entry);
      __ add_d(A3, A1, A2);
      __ add_d(A2, A0, A2);
      bs->copy_load_at(_masm, decorators, type, 16, F0, Address(A0, 0),   gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, F1, Address(A2, -16), gct1, gct2, gcvt1);

      __ andi(T1, A3, 15);
      __ sub_d(A2, A2, T1);
      __ sub_d(A5, A3, T1);

      __ addi_d(A4, A0, 128);
      __ bgeu(A4, A2, le64);

      __ bind(loop);
      bs->copy_load_at(_masm, decorators, type, 16, FT0, Address(A2, -16),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT1, Address(A2, -32),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT2, Address(A2, -48),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT3, Address(A2, -64),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT4, Address(A2, -80),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT5, Address(A2, -96),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT6, Address(A2, -112), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT7, Address(A2, -128), gct1, gct2, gcvt1);
      __ addi_d(A2, A2, -128);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -16),  FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -32),  FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -48),  FT2, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -64),  FT3, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -80),  FT4, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -96),  FT5, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -112), FT6, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -128), FT7, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, -128);
      __ bltu(A4, A2, loop);

      __ bind(le64);
      __ addi_d(A4, A0, 64);
      __ bgeu(A4, A2, le32);
      bs->copy_load_at(_masm, decorators, type, 16, FT0, Address(A2, -16), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT1, Address(A2, -32), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT2, Address(A2, -48), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT3, Address(A2, -64), gct1, gct2, gcvt1);
      __ addi_d(A2, A2, -64);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -16), FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -32), FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -48), FT2, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -64), FT3, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, -64);

      __ bind(le32);
      __ addi_d(A4, A0, 32);
      __ bgeu(A4, A2, le16);
      bs->copy_load_at(_masm, decorators, type, 16, FT0, Address(A2, -16), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 16, FT1, Address(A2, -32), gct1, gct2, gcvt1);
      __ addi_d(A2, A2, -32);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -16), FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -32), FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, -32);

      __ bind(le16);
      __ addi_d(A4, A0, 16);
      __ bgeu(A4, A2, lt16);
      bs->copy_load_at(_masm, decorators, type, 16, FT0, Address(A2, -16), gct1, gct2, gcvt1);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A5, -16), FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);

      __ bind(lt16);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A1, 0),   F0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 16, Address(A3, -16), F1, gct1, gct2, gct3, gct4, gcvt1, gcvt2, false /* need_save_restore */);
    }

    __ move(A0, R0);
    __ jr(RA);
  }

  // conjoint large copy lasx
  void generate_conjoint_large_copy_lasx(DecoratorSet decorators, BasicType type, Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Register gct1 = T2;
    Register gct2 = T3;
    Register gct3 = T4;
    Register gct4 = T5;
    FloatRegister gcvt1 = FT8;
    FloatRegister gcvt2 = FT9;
    BarrierSetAssembler* bs = BarrierSet::barrier_set()->barrier_set_assembler();

    {
      UnsafeMemoryAccessMark umam(this, true, true);
      Label loop, le128, le64, le32, lt32;

      __ bind(entry);
      __ add_d(A3, A1, A2);
      __ add_d(A2, A0, A2);
      bs->copy_load_at(_masm, decorators, type, 32, F0, Address(A0, 0),   gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, F1, Address(A2, -32), gct1, gct2, gcvt1);

      __ andi(T1, A3, 31);
      __ sub_d(A2, A2, T1);
      __ sub_d(A5, A3, T1);

      __ addi_d(A4, A0, 256);
      __ bgeu(A4, A2, le128);

      __ bind(loop);
      bs->copy_load_at(_masm, decorators, type, 32, FT0, Address(A2, -32),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT1, Address(A2, -64),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT2, Address(A2, -96),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT3, Address(A2, -128), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT4, Address(A2, -160), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT5, Address(A2, -192), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT6, Address(A2, -224), gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT7, Address(A2, -256), gct1, gct2, gcvt1);
      __ addi_d(A2, A2, -256);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -32),  FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -64),  FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -96),  FT2, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -128), FT3, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -160), FT4, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -192), FT5, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -224), FT6, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -256), FT7, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, -256);
      __ bltu(A4, A2, loop);

      __ bind(le128);
      __ addi_d(A4, A0, 128);
      __ bgeu(A4, A2, le64);
      bs->copy_load_at(_masm, decorators, type, 32, FT0, Address(A2, -32),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT1, Address(A2, -64),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT2, Address(A2, -96),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT3, Address(A2, -128), gct1, gct2, gcvt1);
      __ addi_d(A2, A2, -128);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -32),  FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -64),  FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -96),  FT2, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -128), FT3, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, -128);

      __ bind(le64);
      __ addi_d(A4, A0, 64);
      __ bgeu(A4, A2, le32);
      bs->copy_load_at(_masm, decorators, type, 32, FT0, Address(A2, -32),  gct1, gct2, gcvt1);
      bs->copy_load_at(_masm, decorators, type, 32, FT1, Address(A2, -64),  gct1, gct2, gcvt1);
      __ addi_d(A2, A2, -64);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -32),  FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -64),  FT1, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      __ addi_d(A5, A5, -64);

      __ bind(le32);
      __ addi_d(A4, A0, 32);
      __ bgeu(A4, A2, lt32);
      bs->copy_load_at(_masm, decorators, type, 32, FT0, Address(A2, -32), gct1, gct2, gcvt1);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A5, -32), FT0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);

      __ bind(lt32);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A1, 0),   F0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
      bs->copy_store_at(_masm, decorators, type, 32, Address(A3, -32), F1, gct1, gct2, gct3, gct4, gcvt1, gcvt2, false /* need_save_restore */);
    }

    __ move(A0, R0);
    __ jr(RA);
  }

  // Byte small copy: less than { int:9, lsx:17, lasx:33 } elements.
  void generate_byte_small_copy(Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Label L;
    __ bind(entry);
    __ lipc(AT, L);
    __ slli_d(A2, A2, 5);
    __ add_d(AT, AT, A2);
    __ jr(AT);

    __ bind(L);
    // 0:
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 1:
    __ ld_b(AT, A0, 0);
    __ st_b(AT, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 2:
    __ ld_h(AT, A0, 0);
    __ st_h(AT, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 3:
    __ ld_h(AT, A0, 0);
    __ ld_b(A2, A0, 2);
    __ st_h(AT, A1, 0);
    __ st_b(A2, A1, 2);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 4:
    __ ld_w(AT, A0, 0);
    __ st_w(AT, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 5:
    __ ld_w(AT, A0, 0);
    __ ld_b(A2, A0, 4);
    __ st_w(AT, A1, 0);
    __ st_b(A2, A1, 4);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 6:
    __ ld_w(AT, A0, 0);
    __ ld_h(A2, A0, 4);
    __ st_w(AT, A1, 0);
    __ st_h(A2, A1, 4);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 7:
    __ ld_w(AT, A0, 0);
    __ ld_w(A2, A0, 3);
    __ st_w(AT, A1, 0);
    __ st_w(A2, A1, 3);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 8:
    __ ld_d(AT, A0, 0);
    __ st_d(AT, A1, 0);
    __ move(A0, R0);
    __ jr(RA);

    if (!UseLSX)
        return;

    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 9:
    __ ld_d(AT, A0, 0);
    __ ld_b(A2, A0, 8);
    __ st_d(AT, A1, 0);
    __ st_b(A2, A1, 8);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 10:
    __ ld_d(AT, A0, 0);
    __ ld_h(A2, A0, 8);
    __ st_d(AT, A1, 0);
    __ st_h(A2, A1, 8);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 11:
    __ ld_d(AT, A0, 0);
    __ ld_w(A2, A0, 7);
    __ st_d(AT, A1, 0);
    __ st_w(A2, A1, 7);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 12:
    __ ld_d(AT, A0, 0);
    __ ld_w(A2, A0, 8);
    __ st_d(AT, A1, 0);
    __ st_w(A2, A1, 8);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 13:
    __ ld_d(AT, A0, 0);
    __ ld_d(A2, A0, 5);
    __ st_d(AT, A1, 0);
    __ st_d(A2, A1, 5);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 14:
    __ ld_d(AT, A0, 0);
    __ ld_d(A2, A0, 6);
    __ st_d(AT, A1, 0);
    __ st_d(A2, A1, 6);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 15:
    __ ld_d(AT, A0, 0);
    __ ld_d(A2, A0, 7);
    __ st_d(AT, A1, 0);
    __ st_d(A2, A1, 7);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 16:
    __ vld(F0, A0, 0);
    __ vst(F0, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    if (!UseLASX)
        return;

    // 17:
    __ vld(F0, A0, 0);
    __ ld_b(AT, A0, 16);
    __ vst(F0, A1, 0);
    __ st_b(AT, A1, 16);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 18:
    __ vld(F0, A0, 0);
    __ ld_h(AT, A0, 16);
    __ vst(F0, A1, 0);
    __ st_h(AT, A1, 16);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 19:
    __ vld(F0, A0, 0);
    __ ld_w(AT, A0, 15);
    __ vst(F0, A1, 0);
    __ st_w(AT, A1, 15);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 20:
    __ vld(F0, A0, 0);
    __ ld_w(AT, A0, 16);
    __ vst(F0, A1, 0);
    __ st_w(AT, A1, 16);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 21:
    __ vld(F0, A0, 0);
    __ ld_d(AT, A0, 13);
    __ vst(F0, A1, 0);
    __ st_d(AT, A1, 13);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 22:
    __ vld(F0, A0, 0);
    __ ld_d(AT, A0, 14);
    __ vst(F0, A1, 0);
    __ st_d(AT, A1, 14);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 23:
    __ vld(F0, A0, 0);
    __ ld_d(AT, A0, 15);
    __ vst(F0, A1, 0);
    __ st_d(AT, A1, 15);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 24:
    __ vld(F0, A0, 0);
    __ ld_d(AT, A0, 16);
    __ vst(F0, A1, 0);
    __ st_d(AT, A1, 16);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 25:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 9);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 9);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 26:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 10);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 10);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 27:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 11);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 11);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 28:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 12);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 12);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 29:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 13);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 13);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 30:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 14);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 14);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 31:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 15);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 15);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 32:
    __ xvld(F0, A0, 0);
    __ xvst(F0, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
  }

  // Arguments:
  //   aligned - true => Input and output aligned on a HeapWord == 8-byte boundary
  //             ignored
  //   name    - stub name string
  //
  // Inputs:
  //   A0      - source array address
  //   A1      - destination array address
  //   A2      - element count, treated as ssize_t, can be zero
  //
  // If 'from' and/or 'to' are aligned on 4-, 2-, or 1-byte boundaries,
  // we let the hardware handle it.  The one to eight bytes within words,
  // dwords or qwords that span cache line boundaries will still be loaded
  // and stored atomically.
  //
  // Side Effects:
  //   disjoint_byte_copy_entry is set to the no-overlap entry point
  //   used by generate_conjoint_byte_copy().
  //
  address generate_disjoint_byte_copy(bool aligned, Label &small, Label &large,
                                      const char * name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    if (UseLASX)
      __ sltui(T0, A2, 33);
    else if (UseLSX)
      __ sltui(T0, A2, 17);
    else
      __ sltui(T0, A2, 9);
    __ bnez(T0, small);

    __ b(large);

    return start;
  }

  // Arguments:
  //   aligned - true => Input and output aligned on a HeapWord == 8-byte boundary
  //             ignored
  //   name    - stub name string
  //
  // Inputs:
  //   A0      - source array address
  //   A1      - destination array address
  //   A2      - element count, treated as ssize_t, can be zero
  //
  // If 'from' and/or 'to' are aligned on 4-, 2-, or 1-byte boundaries,
  // we let the hardware handle it.  The one to eight bytes within words,
  // dwords or qwords that span cache line boundaries will still be loaded
  // and stored atomically.
  //
  address generate_conjoint_byte_copy(bool aligned, Label &small, Label &large,
                                      const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    array_overlap_test(StubRoutines::jbyte_disjoint_arraycopy(), 0);

    if (UseLASX)
      __ sltui(T0, A2, 33);
    else if (UseLSX)
      __ sltui(T0, A2, 17);
    else
      __ sltui(T0, A2, 9);
    __ bnez(T0, small);

    __ b(large);

    return start;
  }

  // Short small copy: less than { int:9, lsx:9, lasx:17 } elements.
  void generate_short_small_copy(Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Label L;
    __ bind(entry);
    __ lipc(AT, L);
    __ slli_d(A2, A2, 5);
    __ add_d(AT, AT, A2);
    __ jr(AT);

    __ bind(L);
    // 0:
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 1:
    __ ld_h(AT, A0, 0);
    __ st_h(AT, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 2:
    __ ld_w(AT, A0, 0);
    __ st_w(AT, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 3:
    __ ld_w(AT, A0, 0);
    __ ld_h(A2, A0, 4);
    __ st_w(AT, A1, 0);
    __ st_h(A2, A1, 4);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 4:
    __ ld_d(AT, A0, 0);
    __ st_d(AT, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 5:
    __ ld_d(AT, A0, 0);
    __ ld_h(A2, A0, 8);
    __ st_d(AT, A1, 0);
    __ st_h(A2, A1, 8);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 6:
    __ ld_d(AT, A0, 0);
    __ ld_w(A2, A0, 8);
    __ st_d(AT, A1, 0);
    __ st_w(A2, A1, 8);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 7:
    __ ld_d(AT, A0, 0);
    __ ld_d(A2, A0, 6);
    __ st_d(AT, A1, 0);
    __ st_d(A2, A1, 6);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 8:
    if (UseLSX) {
      __ vld(F0, A0, 0);
      __ vst(F0, A1, 0);
      __ move(A0, R0);
      __ jr(RA);
      __ nop();
      __ nop();
    } else {
      __ ld_d(AT, A0, 0);
      __ ld_d(A2, A0, 8);
      __ st_d(AT, A1, 0);
      __ st_d(A2, A1, 8);
      __ move(A0, R0);
      __ jr(RA);
    }

    if (!UseLASX)
        return;

    __ nop();
    __ nop();

    // 9:
    __ vld(F0, A0, 0);
    __ ld_h(AT, A0, 16);
    __ vst(F0, A1, 0);
    __ st_h(AT, A1, 16);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 10:
    __ vld(F0, A0, 0);
    __ ld_w(AT, A0, 16);
    __ vst(F0, A1, 0);
    __ st_w(AT, A1, 16);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 11:
    __ vld(F0, A0, 0);
    __ ld_d(AT, A0, 14);
    __ vst(F0, A1, 0);
    __ st_d(AT, A1, 14);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 12:
    __ vld(F0, A0, 0);
    __ ld_d(AT, A0, 16);
    __ vst(F0, A1, 0);
    __ st_d(AT, A1, 16);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 13:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 10);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 10);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 14:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 12);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 12);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 15:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 14);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 14);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 16:
    __ xvld(F0, A0, 0);
    __ xvst(F0, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
  }

  // Arguments:
  //   aligned - true => Input and output aligned on a HeapWord == 8-byte boundary
  //             ignored
  //   name    - stub name string
  //
  // Inputs:
  //   A0      - source array address
  //   A1      - destination array address
  //   A2      - element count, treated as ssize_t, can be zero
  //
  // If 'from' and/or 'to' are aligned on 4-, 2-, or 1-byte boundaries,
  // we let the hardware handle it.  The one to eight bytes within words,
  // dwords or qwords that span cache line boundaries will still be loaded
  // and stored atomically.
  //
  // Side Effects:
  //   disjoint_short_copy_entry is set to the no-overlap entry point
  //   used by generate_conjoint_short_copy().
  //
  address generate_disjoint_short_copy(bool aligned, Label &small, Label &large,
                                       const char * name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    if (UseLASX)
      __ sltui(T0, A2, 17);
    else
      __ sltui(T0, A2, 9);
    __ bnez(T0, small);

    __ slli_d(A2, A2, 1);

    __ b(large);

    return start;
  }

  // Arguments:
  //   aligned - true => Input and output aligned on a HeapWord == 8-byte boundary
  //             ignored
  //   name    - stub name string
  //
  // Inputs:
  //   A0      - source array address
  //   A1      - destination array address
  //   A2      - element count, treated as ssize_t, can be zero
  //
  // If 'from' and/or 'to' are aligned on 4- or 2-byte boundaries, we
  // let the hardware handle it.  The two or four words within dwords
  // or qwords that span cache line boundaries will still be loaded
  // and stored atomically.
  //
  address generate_conjoint_short_copy(bool aligned, Label &small, Label &large,
                                       const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    array_overlap_test(StubRoutines::jshort_disjoint_arraycopy(), 1);

    if (UseLASX)
      __ sltui(T0, A2, 17);
    else
      __ sltui(T0, A2, 9);
    __ bnez(T0, small);

    __ slli_d(A2, A2, 1);

    __ b(large);

    return start;
  }

  // Int small copy: less than { int:7, lsx:7, lasx:9 } elements.
  void generate_int_small_copy(Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Label L;
    __ bind(entry);
    __ lipc(AT, L);
    __ slli_d(A2, A2, 5);
    __ add_d(AT, AT, A2);
    __ jr(AT);

    __ bind(L);
    // 0:
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 1:
    __ ld_w(AT, A0, 0);
    __ st_w(AT, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 2:
    __ ld_d(AT, A0, 0);
    __ st_d(AT, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();
    __ nop();
    __ nop();

    // 3:
    __ ld_d(AT, A0, 0);
    __ ld_w(A2, A0, 8);
    __ st_d(AT, A1, 0);
    __ st_w(A2, A1, 8);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 4:
    if (UseLSX) {
      __ vld(F0, A0, 0);
      __ vst(F0, A1, 0);
      __ move(A0, R0);
      __ jr(RA);
      __ nop();
      __ nop();
    } else {
      __ ld_d(AT, A0, 0);
      __ ld_d(A2, A0, 8);
      __ st_d(AT, A1, 0);
      __ st_d(A2, A1, 8);
      __ move(A0, R0);
      __ jr(RA);
    }
    __ nop();
    __ nop();

    // 5:
    if (UseLSX) {
      __ vld(F0, A0, 0);
      __ ld_w(AT, A0, 16);
      __ vst(F0, A1, 0);
      __ st_w(AT, A1, 16);
      __ move(A0, R0);
      __ jr(RA);
      __ nop();
      __ nop();
    } else {
      __ ld_d(AT, A0, 0);
      __ ld_d(A2, A0, 8);
      __ ld_w(A3, A0, 16);
      __ st_d(AT, A1, 0);
      __ st_d(A2, A1, 8);
      __ st_w(A3, A1, 16);
      __ move(A0, R0);
      __ jr(RA);
    }

    // 6:
    if (UseLSX) {
      __ vld(F0, A0, 0);
      __ ld_d(AT, A0, 16);
      __ vst(F0, A1, 0);
      __ st_d(AT, A1, 16);
      __ move(A0, R0);
      __ jr(RA);
      __ nop();
      __ nop();
    } else {
      __ ld_d(AT, A0, 0);
      __ ld_d(A2, A0, 8);
      __ ld_d(A3, A0, 16);
      __ st_d(AT, A1, 0);
      __ st_d(A2, A1, 8);
      __ st_d(A3, A1, 16);
      __ move(A0, R0);
      __ jr(RA);
    }

    if (!UseLASX)
        return;

    // 7:
    __ vld(F0, A0, 0);
    __ vld(F1, A0, 12);
    __ vst(F0, A1, 0);
    __ vst(F1, A1, 12);
    __ move(A0, R0);
    __ jr(RA);
    __ nop();
    __ nop();

    // 8:
    __ xvld(F0, A0, 0);
    __ xvst(F0, A1, 0);
    __ move(A0, R0);
    __ jr(RA);
  }

  // Generate maybe oop copy
  void gen_maybe_oop_copy(bool is_oop, bool disjoint, bool aligned, Label &small,
                          Label &large, const char *name, int small_limit,
                          int log2_elem_size, bool dest_uninitialized = false) {
    Label post, _large;
    DecoratorSet decorators = DECORATORS_NONE;
    BarrierSetAssembler *bs = nullptr;

    if (is_oop) {
      decorators = IN_HEAP | IS_ARRAY;

      if (disjoint) {
        decorators |= ARRAYCOPY_DISJOINT;
      }

      if (aligned) {
        decorators |= ARRAYCOPY_ALIGNED;
      }

      if (dest_uninitialized) {
        decorators |= IS_DEST_UNINITIALIZED;
      }

      __ push(RegSet::of(RA));

      bs = BarrierSet::barrier_set()->barrier_set_assembler();
      bs->arraycopy_prologue(_masm, decorators, is_oop, A0, A1, A2, RegSet::of(A0, A1, A2));

      __ push(RegSet::of(A1, A2));
    }

    __ sltui(T0, A2, small_limit);
    if (is_oop) {
      __ beqz(T0, _large);
      __ bl(small);
      __ b(post);
    } else {
      __ bnez(T0, small);
    }

    __ bind(_large);
    __ slli_d(A2, A2, log2_elem_size);

    if (is_oop) {
      __ bl(large);
    } else {
      __ b(large);
    }

    if (is_oop) {
      __ bind(post);
      __ pop(RegSet::of(A1, A2));

      bs->arraycopy_epilogue(_masm, decorators, is_oop, A1, A2, T1, RegSet());

      __ pop(RegSet::of(RA));
      __ move(A0, R0);
      __ jr(RA);
    }
  }

  // Arguments:
  //   aligned - true => Input and output aligned on a HeapWord == 8-byte boundary
  //             ignored
  //   is_oop  - true => oop array, so generate store check code
  //   name    - stub name string
  //
  // Inputs:
  //   A0      - source array address
  //   A1      - destination array address
  //   A2      - element count, treated as ssize_t, can be zero
  //
  // If 'from' and/or 'to' are aligned on 4-byte boundaries, we let
  // the hardware handle it.  The two dwords within qwords that span
  // cache line boundaries will still be loaded and stored atomically.
  //
  // Side Effects:
  //   disjoint_int_copy_entry is set to the no-overlap entry point
  //   used by generate_conjoint_int_oop_copy().
  //
  address generate_disjoint_int_oop_copy(bool aligned, bool is_oop, Label &small,
                                         Label &large, const char *name, int small_limit,
                                         bool dest_uninitialized = false) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    gen_maybe_oop_copy(is_oop, true, aligned, small, large, name,
                       small_limit, 2, dest_uninitialized);

    return start;
  }

  // Arguments:
  //   aligned - true => Input and output aligned on a HeapWord == 8-byte boundary
  //             ignored
  //   is_oop  - true => oop array, so generate store check code
  //   name    - stub name string
  //
  // Inputs:
  //   A0      - source array address
  //   A1      - destination array address
  //   A2      - element count, treated as ssize_t, can be zero
  //
  // If 'from' and/or 'to' are aligned on 4-byte boundaries, we let
  // the hardware handle it.  The two dwords within qwords that span
  // cache line boundaries will still be loaded and stored atomically.
  //
  address generate_conjoint_int_oop_copy(bool aligned, bool is_oop, Label &small,
                                         Label &large, const char *name, int small_limit,
                                         bool dest_uninitialized = false) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    if (is_oop) {
      array_overlap_test(StubRoutines::oop_disjoint_arraycopy(), 2);
    } else {
      array_overlap_test(StubRoutines::jint_disjoint_arraycopy(), 2);
    }

    gen_maybe_oop_copy(is_oop, false, aligned, small, large, name,
                       small_limit, 2, dest_uninitialized);

    return start;
  }

  // Long small copy: less than { int:4, lsx:4, lasx:5 } elements.
  void generate_long_small_copy(DecoratorSet decorators, BasicType type, Label &entry, const char *name) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);

    Register gct1 = T2;
    Register gct2 = T3;
    Register gct3 = T4;
    Register gct4 = T5;
    FloatRegister gcvt1 = FT8;
    FloatRegister gcvt2 = FT9;
    BarrierSetAssembler* bs = BarrierSet::barrier_set()->barrier_set_assembler();

    Label L, L1, L2, L3, L4;
    __ bind(entry);
    __ beqz(A2, L);
    __ li(SCR1, 1);
    __ beq(A2, SCR1, L1);
    __ li(SCR1, 2);
    __ beq(A2, SCR1, L2);
    __ li(SCR1, 3);
    __ beq(A2, SCR1, L3);
    __ li(SCR1, 4);
    __ beq(A2, SCR1, L4);

    __ bind(L);
    // 0:
    __ move(A0, R0);
    __ jr(RA);

    {
      UnsafeMemoryAccessMark umam(this, true, true);
      // 1:
      __ bind(L1);
      bs->copy_load_at(_masm, decorators, type, 8, T8, Address(A0, 0), gct1);
      bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 0), T8, gct1, gct2, gct3);
      __ move(A0, R0);
      __ jr(RA);

      // 2:
      __ bind(L2);
      if (UseLSX && !UseZGC) {
        bs->copy_load_at(_masm, decorators, type, 16, F0, Address(A0, 0), gct1, gct2, gcvt1);
        bs->copy_store_at(_masm, decorators, type, 16, Address(A1, 0), F0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
        __ move(A0, R0);
        __ jr(RA);
      } else {
        bs->copy_load_at(_masm, decorators, type, 8, T8, Address(A0, 0), gct1);
        bs->copy_load_at(_masm, decorators, type, 8, A2, Address(A0, 8), gct1);
        bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 0), T8, gct1, gct2, gct3);
        bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 8), A2, gct1, gct2, gct3);
        __ move(A0, R0);
        __ jr(RA);
      }

      // 3:
      __ bind(L3);
      if (UseLSX && !UseZGC) {
        bs->copy_load_at(_masm, decorators, type, 16, F0, Address(A0, 0), gct1, gct2, gcvt1);
        bs->copy_load_at(_masm, decorators, type, 8,  T8, Address(A0, 16), gct1);
        bs->copy_store_at(_masm, decorators, type, 16, Address(A1, 0), F0, gct1, gct2, gct3, gct4, gcvt1, gcvt2);
        bs->copy_store_at(_masm, decorators, type, 8,  Address(A1, 16), T8, gct1, gct2, gct3);
        __ move(A0, R0);
        __ jr(RA);
      } else {
        bs->copy_load_at(_masm, decorators, type, 8, T8, Address(A0, 0),  gct1);
        bs->copy_load_at(_masm, decorators, type, 8, A2, Address(A0, 8),  gct1);
        bs->copy_load_at(_masm, decorators, type, 8, A3, Address(A0, 16), gct1);
        bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 0),  T8, gct1, gct2, gct3);
        bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 8),  A2, gct1, gct2, gct3);
        bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 16), A3, gct1, gct2, gct3);
        __ move(A0, R0);
        __ jr(RA);
      }

      __ bind(L4);
      // 4:
      if (UseLASX) {
        bs->copy_load_at(_masm, decorators, type, 32, F0, Address(A0, 0), gct1, gct2, gcvt1);
        bs->copy_store_at(_masm, decorators, type, 32, Address(A1, 0), F0, gct1, gct2, gct3, gct4, gcvt1, gcvt2, false /* need_save_restore */);
      } else {
        bs->copy_load_at(_masm, decorators, type, 8, T8, Address(A0, 0),  gct1);
        bs->copy_load_at(_masm, decorators, type, 8, A2, Address(A0, 8),  gct1);
        bs->copy_load_at(_masm, decorators, type, 8, A3, Address(A0, 16), gct1);
        bs->copy_load_at(_masm, decorators, type, 8, A4, Address(A0, 32), gct1);
        bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 0),  T8, gct1, gct2, gct3);
        bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 8),  A2, gct1, gct2, gct3);
        bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 16), A3, gct1, gct2, gct3);
        bs->copy_store_at(_masm, decorators, type, 8, Address(A1, 32), A4, gct1, gct2, gct3);
      }
    }

    __ move(A0, R0);
    __ jr(RA);
  }

  // Arguments:
  //   aligned - true => Input and output aligned on a HeapWord == 8-byte boundary
  //             ignored
  //   is_oop  - true => oop array, so generate store check code
  //   name    - stub name string
  //
  // Inputs:
  //   A0      - source array address
  //   A1      - destination array address
  //   A2      - element count, treated as ssize_t, can be zero
  //
  // If 'from' and/or 'to' are aligned on 4-byte boundaries, we let
  // the hardware handle it.  The two dwords within qwords that span
  // cache line boundaries will still be loaded and stored atomically.
  //
  // Side Effects:
  //   disjoint_int_copy_entry is set to the no-overlap entry point
  //   used by generate_conjoint_int_oop_copy().
  //
  address generate_disjoint_long_oop_copy(bool aligned, bool is_oop, Label &small,
                                          Label &large, const char *name, int small_limit,
                                          bool dest_uninitialized = false) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    gen_maybe_oop_copy(is_oop, true, aligned, small, large, name,
                       small_limit, 3, dest_uninitialized);

    return start;
  }

  // Arguments:
  //   aligned - true => Input and output aligned on a HeapWord == 8-byte boundary
  //             ignored
  //   is_oop  - true => oop array, so generate store check code
  //   name    - stub name string
  //
  // Inputs:
  //   A0      - source array address
  //   A1      - destination array address
  //   A2      - element count, treated as ssize_t, can be zero
  //
  // If 'from' and/or 'to' are aligned on 4-byte boundaries, we let
  // the hardware handle it.  The two dwords within qwords that span
  // cache line boundaries will still be loaded and stored atomically.
  //
  address generate_conjoint_long_oop_copy(bool aligned, bool is_oop, Label &small,
                                          Label &large, const char *name, int small_limit,
                                          bool dest_uninitialized = false) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    if (is_oop) {
      array_overlap_test(StubRoutines::oop_disjoint_arraycopy(dest_uninitialized /* ZGC */), 3);
    } else {
      array_overlap_test(StubRoutines::jlong_disjoint_arraycopy(), 3);
    }

    gen_maybe_oop_copy(is_oop, false, aligned, small, large, name,
                       small_limit, 3, dest_uninitialized);

    return start;
  }

  // Helper for generating a dynamic type check.
  // Smashes scratch1, scratch2.
  void generate_type_check(Register sub_klass,
                           Register super_check_offset,
                           Register super_klass,
                           Register tmp1,
                           Register tmp2,
                           Label& L_success) {
    assert_different_registers(sub_klass, super_check_offset, super_klass);

    __ block_comment("type_check:");

    Label L_miss;

    __ check_klass_subtype_fast_path(sub_klass, super_klass, tmp1,       &L_success, &L_miss, nullptr,
                                     super_check_offset);
    __ check_klass_subtype_slow_path<false>(sub_klass, super_klass, tmp1, tmp2, &L_success, nullptr);

    // Fall through on failure!
    __ bind(L_miss);
  }

  //
  //  Generate checkcasting array copy stub
  //
  //  Input:
  //    A0   - source array address
  //    A1   - destination array address
  //    A2   - element count, treated as ssize_t, can be zero
  //    A3   - size_t ckoff (super_check_offset)
  //    A4   - oop ckval (super_klass)
  //
  //  Output:
  //    V0 ==  0  -  success
  //    V0 == -1^K - failure, where K is partial transfer count
  //
  address generate_checkcast_copy(const char *name, bool dest_uninitialized = false) {
    Label L_load_element, L_store_element, L_do_card_marks, L_done, L_done_pop;

    // Input registers (after setup_arg_regs)
    const Register from        = A0; // source array address
    const Register to          = A1; // destination array address
    const Register count       = A2; // elementscount
    const Register ckoff       = A3; // super_check_offset
    const Register ckval       = A4; // super_klass

    RegSet wb_pre_saved_regs = RegSet::range(A0, A4);
    RegSet wb_post_saved_regs = RegSet::of(count);

    // Registers used as temps (S0, S1, S2, S3 are save-on-entry)
    const Register copied_oop  = S0; // actual oop copied
    const Register count_save  = S1; // orig elementscount
    const Register start_to    = S2; // destination array start address
    const Register oop_klass   = S3; // oop._klass
    const Register tmp1        = A5;
    const Register tmp2        = A6;
    const Register tmp3        = A7;

    //---------------------------------------------------------------
    // Assembler stub will be used for this call to arraycopy
    // if the two arrays are subtypes of Object[] but the
    // destination array type is not equal to or a supertype
    // of the source type.  Each element must be separately
    // checked.

    assert_different_registers(from, to, count, ckoff, ckval, start_to,
                               copied_oop, oop_klass, count_save);

    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    // caller guarantees that the arrays really are different
    // otherwise, we would have to make conjoint checks

    // Caller of this entry point must set up the argument registers.
    __ block_comment("Entry:");

    // Empty array:  Nothing to do.
    __ beqz(count, L_done);

    __ push(RegSet::of(S0, S1, S2, S3) + RA);

#ifdef ASSERT
    __ block_comment("assert consistent ckoff/ckval");
    // The ckoff and ckval must be mutually consistent,
    // even though caller generates both.
    { Label L;
      int sco_offset = in_bytes(Klass::super_check_offset_offset());
      __ ld_w(start_to, Address(ckval, sco_offset));
      __ beq(ckoff, start_to, L);
      __ stop("super_check_offset inconsistent");
      __ bind(L);
    }
#endif //ASSERT

    DecoratorSet decorators = IN_HEAP | IS_ARRAY | ARRAYCOPY_CHECKCAST | ARRAYCOPY_DISJOINT;
    bool is_oop = true;
    if (dest_uninitialized) {
      decorators |= IS_DEST_UNINITIALIZED;
    }

    BarrierSetAssembler *bs = BarrierSet::barrier_set()->barrier_set_assembler();
    bs->arraycopy_prologue(_masm, decorators, is_oop, from, to, count, wb_pre_saved_regs);

    // save the original count
    __ move(count_save, count);

    // Copy from low to high addresses
    __ move(start_to, to); // Save destination array start address
    __ b(L_load_element);

    // ======== begin loop ========
    // (Loop is rotated; its entry is L_load_element.)
    // Loop control:
    //   for (; count != 0; count--) {
    //     copied_oop = load_heap_oop(from++);
    //     ... generate_type_check ...;
    //     store_heap_oop(to++, copied_oop);
    //   }
    __ align(OptoLoopAlignment);

    __ bind(L_store_element);
    bs->copy_store_at(_masm, decorators, T_OBJECT, UseCompressedOops ? 4 : 8,
                      Address(to, 0), copied_oop,
                      tmp1, tmp2, tmp3);
    __ addi_d(to, to, UseCompressedOops ? 4 : 8);
    __ addi_d(count, count, -1);
    __ beqz(count, L_do_card_marks);

    // ======== loop entry is here ========
    __ bind(L_load_element);
    bs->copy_load_at(_masm, decorators, T_OBJECT, UseCompressedOops ? 4 : 8,
                     copied_oop, Address(from, 0),
                     tmp1);
    __ addi_d(from, from, UseCompressedOops ? 4 : 8);
    __ beqz(copied_oop, L_store_element);

    __ load_klass(oop_klass, copied_oop); // query the object klass
    generate_type_check(oop_klass, ckoff, ckval, tmp1, tmp2, L_store_element);
    // ======== end loop ========

    // Register count = remaining oops, count_orig = total oops.
    // Emit GC store barriers for the oops we have copied and report
    // their number to the caller.

    __ sub_d(tmp1, count_save, count); // K = partially copied oop count
    __ nor(count, tmp1, R0); // report (-1^K) to caller
    __ beqz(tmp1, L_done_pop);

    __ bind(L_do_card_marks);

    bs->arraycopy_epilogue(_masm, decorators, is_oop, start_to, count_save, tmp2, wb_post_saved_regs);

    __ bind(L_done_pop);
    __ pop(RegSet::of(S0, S1, S2, S3) + RA);

#ifndef PRODUCT
    __ li(SCR2, (address)&SharedRuntime::_checkcast_array_copy_ctr);
    __ increment(Address(SCR2, 0), 1);
#endif

    __ bind(L_done);
    __ move(A0, count);
    __ jr(RA);

    return start;
  }

  //
  //  Generate 'unsafe' array copy stub
  //  Though just as safe as the other stubs, it takes an unscaled
  //  size_t argument instead of an element count.
  //
  //  Input:
  //    A0   - source array address
  //    A1   - destination array address
  //    A2   - byte count, treated as ssize_t, can be zero
  //
  // Examines the alignment of the operands and dispatches
  // to a long, int, short, or byte copy loop.
  //
  address generate_unsafe_copy(const char *name) {
    Label L_long_aligned, L_int_aligned, L_short_aligned;
    Register s = A0, d = A1, count = A2;

    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    address start = __ pc();

    __ orr(AT, s, d);
    __ orr(AT, AT, count);

    __ andi(AT, AT, BytesPerLong-1);
    __ beqz(AT, L_long_aligned);
    __ andi(AT, AT, BytesPerInt-1);
    __ beqz(AT, L_int_aligned);
    __ andi(AT, AT, BytesPerShort-1);
    __ beqz(AT, L_short_aligned);
    __ b(StubRoutines::_jbyte_arraycopy);

    __ bind(L_short_aligned);
    __ srli_d(count, count, LogBytesPerShort);  // size => short_count
    __ b(StubRoutines::_jshort_arraycopy);
    __ bind(L_int_aligned);
    __ srli_d(count, count, LogBytesPerInt);    // size => int_count
    __ b(StubRoutines::_jint_arraycopy);
    __ bind(L_long_aligned);
    __ srli_d(count, count, LogBytesPerLong);   // size => long_count
    __ b(StubRoutines::_jlong_arraycopy);

    return start;
  }

  // Perform range checks on the proposed arraycopy.
  // Kills temp, but nothing else.
  // Also, clean the sign bits of src_pos and dst_pos.
  void arraycopy_range_checks(Register src,     // source array oop (A0)
                              Register src_pos, // source position (A1)
                              Register dst,     // destination array oo (A2)
                              Register dst_pos, // destination position (A3)
                              Register length,
                              Register temp,
                              Label& L_failed) {
    __ block_comment("arraycopy_range_checks:");

    assert_different_registers(SCR1, temp);

    // if (src_pos + length > arrayOop(src)->length()) FAIL;
    __ ld_w(SCR1, Address(src, arrayOopDesc::length_offset_in_bytes()));
    __ add_w(temp, length, src_pos);
    __ bltu(SCR1, temp, L_failed);

    //  if (dst_pos + length > arrayOop(dst)->length())  FAIL;
    __ ld_w(SCR1, Address(dst, arrayOopDesc::length_offset_in_bytes()));
    __ add_w(temp, length, dst_pos);
    __ bltu(SCR1, temp, L_failed);

    // Have to clean up high 32 bits of 'src_pos' and 'dst_pos'.
    __ move(src_pos, src_pos);
    __ move(dst_pos, dst_pos);

    __ block_comment("arraycopy_range_checks done");
  }

  //
  //  Generate generic array copy stubs
  //
  //  Input:
  //    A0    -  src oop
  //    A1    -  src_pos (32-bits)
  //    A2    -  dst oop
  //    A3    -  dst_pos (32-bits)
  //    A4    -  element count (32-bits)
  //
  //  Output:
  //    V0 ==  0  -  success
  //    V0 == -1^K - failure, where K is partial transfer count
  //
  address generate_generic_copy(const char *name) {
    Label L_failed, L_objArray;
    Label L_copy_bytes, L_copy_shorts, L_copy_ints, L_copy_longs;

    // Input registers
    const Register src        = A0; // source array oop
    const Register src_pos    = A1; // source position
    const Register dst        = A2; // destination array oop
    const Register dst_pos    = A3; // destination position
    const Register length     = A4;

    // Registers used as temps
    const Register dst_klass  = A5;

    __ align(CodeEntryAlignment);

    StubCodeMark mark(this, "StubRoutines", name);

    address start = __ pc();

#ifndef PRODUCT
    // bump this on entry, not on exit:
    __ li(SCR2, (address)&SharedRuntime::_generic_array_copy_ctr);
    __ increment(Address(SCR2, 0), 1);
#endif

    //-----------------------------------------------------------------------
    // Assembler stub will be used for this call to arraycopy
    // if the following conditions are met:
    //
    // (1) src and dst must not be null.
    // (2) src_pos must not be negative.
    // (3) dst_pos must not be negative.
    // (4) length  must not be negative.
    // (5) src klass and dst klass should be the same and not null.
    // (6) src and dst should be arrays.
    // (7) src_pos + length must not exceed length of src.
    // (8) dst_pos + length must not exceed length of dst.
    //

    // if (src == nullptr) return -1;
    __ beqz(src, L_failed);

    // if (src_pos < 0) return -1;
    __ blt(src_pos, R0, L_failed);

    // if (dst == nullptr) return -1;
    __ beqz(dst, L_failed);

    // if (dst_pos < 0) return -1;
    __ blt(dst_pos, R0, L_failed);

    // registers used as temp
    const Register scratch_length    = T0; // elements count to copy
    const Register scratch_src_klass = T1; // array klass
    const Register lh                = T2; // layout helper
    const Register tmp1              = T3;
    const Register tmp2              = T4;

    // if (length < 0) return -1;
    __ move(scratch_length, length); // length (elements count, 32-bits value)
    __ blt(scratch_length, R0, L_failed);

    __ load_klass(scratch_src_klass, src);
#ifdef ASSERT
    // assert(src->klass() != nullptr);
    {
      __ block_comment("assert klasses not null {");
      Label L1, L2;
      __ bnez(scratch_src_klass, L2); // it is broken if klass is null
      __ bind(L1);
      __ stop("broken null klass");
      __ bind(L2);
      __ load_klass(SCR2, dst);
      __ beqz(SCR2, L1);     // this would be broken also
      __ block_comment("} assert klasses not null done");
    }
#endif

    // Load layout helper (32-bits)
    //
    //  |array_tag|     | header_size | element_type |     |log2_element_size|
    // 32        30    24            16              8     2                 0
    //
    //   array_tag: typeArray = 0x3, objArray = 0x2, non-array = 0x0
    //

    const int lh_offset = in_bytes(Klass::layout_helper_offset());

    // Handle objArrays completely differently...
    const jint objArray_lh = Klass::array_layout_helper(T_OBJECT);
    __ ld_w(lh, Address(scratch_src_klass, lh_offset));
    __ li(SCR1, objArray_lh);
    __ xorr(SCR2, lh, SCR1);
    __ beqz(SCR2, L_objArray);

    // if (src->klass() != dst->klass()) return -1;
    __ load_klass(SCR2, dst);
    __ xorr(SCR2, SCR2, scratch_src_klass);
    __ bnez(SCR2, L_failed);

    // if (!src->is_Array()) return -1;
    __ bge(lh, R0, L_failed); // i.e. (lh >= 0)

    // At this point, it is known to be a typeArray (array_tag 0x3).
#ifdef ASSERT
    {
      __ block_comment("assert primitive array {");
      Label L;
      __ li(SCR2, (int)(Klass::_lh_array_tag_type_value << Klass::_lh_array_tag_shift));
      __ bge(lh, SCR2, L);
      __ stop("must be a primitive array");
      __ bind(L);
      __ block_comment("} assert primitive array done");
    }
#endif

    arraycopy_range_checks(src, src_pos, dst, dst_pos, scratch_length, SCR2, L_failed);

    // TypeArrayKlass
    //
    // src_addr = (src + array_header_in_bytes()) + (src_pos << log2elemsize);
    // dst_addr = (dst + array_header_in_bytes()) + (dst_pos << log2elemsize);
    //

    const Register scr1_offset = SCR1; // array offset
    const Register elsize = lh; // element size

    __ bstrpick_d(scr1_offset, lh, Klass::_lh_header_size_shift +
                  exact_log2(Klass::_lh_header_size_mask+1) - 1,
                  Klass::_lh_header_size_shift); // array_offset
    __ add_d(src, src, scr1_offset); // src array offset
    __ add_d(dst, dst, scr1_offset); // dst array offset
    __ block_comment("choose copy loop based on element size");

    // next registers should be set before the jump to corresponding stub
    const Register from     = A0; // source array address
    const Register to       = A1; // destination array address
    const Register count    = A2; // elements count

    // 'from', 'to', 'count' registers should be set in such order
    // since they are the same as 'src', 'src_pos', 'dst'.

    assert(Klass::_lh_log2_element_size_shift == 0, "fix this code");

    // The possible values of elsize are 0-3, i.e. exact_log2(element
    // size in bytes).  We do a simple bitwise binary search.
    __ bind(L_copy_bytes);
    __ andi(tmp1, elsize, 2);
    __ bnez(tmp1, L_copy_ints);
    __ andi(tmp1, elsize, 1);
    __ bnez(tmp1, L_copy_shorts);
    __ lea(from, Address(src, src_pos, Address::no_scale)); // src_addr
    __ lea(to,   Address(dst, dst_pos, Address::no_scale)); // dst_addr
    __ move(count, scratch_length); // length
    __ b(StubRoutines::_jbyte_arraycopy);

    __ bind(L_copy_shorts);
    __ lea(from, Address(src, src_pos, Address::times_2)); // src_addr
    __ lea(to,   Address(dst, dst_pos, Address::times_2)); // dst_addr
    __ move(count, scratch_length); // length
    __ b(StubRoutines::_jshort_arraycopy);

    __ bind(L_copy_ints);
    __ andi(tmp1, elsize, 1);
    __ bnez(tmp1, L_copy_longs);
    __ lea(from, Address(src, src_pos, Address::times_4)); // src_addr
    __ lea(to,   Address(dst, dst_pos, Address::times_4)); // dst_addr
    __ move(count, scratch_length); // length
    __ b(StubRoutines::_jint_arraycopy);

    __ bind(L_copy_longs);
#ifdef ASSERT
    {
      __ block_comment("assert long copy {");
      Label L;
      __ andi(lh, lh, Klass::_lh_log2_element_size_mask); // lh -> elsize
      __ li(tmp1, LogBytesPerLong);
      __ beq(elsize, tmp1, L);
      __ stop("must be long copy, but elsize is wrong");
      __ bind(L);
      __ block_comment("} assert long copy done");
    }
#endif
    __ lea(from, Address(src, src_pos, Address::times_8)); // src_addr
    __ lea(to,   Address(dst, dst_pos, Address::times_8)); // dst_addr
    __ move(count, scratch_length); // length
    __ b(StubRoutines::_jlong_arraycopy);

    // ObjArrayKlass
    __ bind(L_objArray);
    // live at this point:  scratch_src_klass, scratch_length, src[_pos], dst[_pos]

    Label L_plain_copy, L_checkcast_copy;
    //  test array classes for subtyping
    __ load_klass(tmp1, dst);
    __ bne(scratch_src_klass, tmp1, L_checkcast_copy); // usual case is exact equality

    // Identically typed arrays can be copied without element-wise checks.
    arraycopy_range_checks(src, src_pos, dst, dst_pos, scratch_length, SCR2, L_failed);

    __ lea(from, Address(src, src_pos, Address::ScaleFactor(LogBytesPerHeapOop)));
    __ addi_d(from, from, arrayOopDesc::base_offset_in_bytes(T_OBJECT));
    __ lea(to, Address(dst, dst_pos, Address::ScaleFactor(LogBytesPerHeapOop)));
    __ addi_d(to, to, arrayOopDesc::base_offset_in_bytes(T_OBJECT));
    __ move(count, scratch_length); // length
    __ bind(L_plain_copy);
    __ b(StubRoutines::_oop_arraycopy);

    __ bind(L_checkcast_copy);
    // live at this point:  scratch_src_klass, scratch_length, tmp1 (dst_klass)
    {
      // Before looking at dst.length, make sure dst is also an objArray.
      __ ld_w(SCR1, Address(tmp1, lh_offset));
      __ li(SCR2, objArray_lh);
      __ xorr(SCR1, SCR1, SCR2);
      __ bnez(SCR1, L_failed);

      // It is safe to examine both src.length and dst.length.
      arraycopy_range_checks(src, src_pos, dst, dst_pos, scratch_length, tmp1, L_failed);

      __ load_klass(dst_klass, dst); // reload

      // Marshal the base address arguments now, freeing registers.
      __ lea(from, Address(src, src_pos, Address::ScaleFactor(LogBytesPerHeapOop)));
      __ addi_d(from, from, arrayOopDesc::base_offset_in_bytes(T_OBJECT));
      __ lea(to, Address(dst, dst_pos, Address::ScaleFactor(LogBytesPerHeapOop)));
      __ addi_d(to, to, arrayOopDesc::base_offset_in_bytes(T_OBJECT));
      __ move(count, length); // length (reloaded)
      Register sco_temp = A3; // this register is free now
      assert_different_registers(from, to, count, sco_temp, dst_klass, scratch_src_klass);
      // assert_clean_int(count, sco_temp);

      // Generate the type check.
      const int sco_offset = in_bytes(Klass::super_check_offset_offset());
      __ ld_w(sco_temp, Address(dst_klass, sco_offset));

      // Smashes SCR1, SCR2
      generate_type_check(scratch_src_klass, sco_temp, dst_klass, tmp1, tmp2, L_plain_copy);

      // Fetch destination element klass from the ObjArrayKlass header.
      int ek_offset = in_bytes(ObjArrayKlass::element_klass_offset());
      __ ld_d(dst_klass, Address(dst_klass, ek_offset));
      __ ld_w(sco_temp, Address(dst_klass, sco_offset));

      // the checkcast_copy loop needs two extra arguments:
      assert(A3 == sco_temp, "#3 already in place");
      // Set up arguments for checkcast_arraycopy.
      __ move(A4, dst_klass); // dst.klass.element_klass
      __ b(StubRoutines::_checkcast_arraycopy);
    }

    __ bind(L_failed);
    __ li(V0, -1);
    __ jr(RA);

    return start;
  }

  void generate_arraycopy_stubs() {
    Label disjoint_large_copy, conjoint_large_copy;
#if INCLUDE_ZGC
    Label disjoint_large_copy_oop, conjoint_large_copy_oop;
    Label disjoint_large_copy_oop_uninit, conjoint_large_copy_oop_uninit;
#endif
    Label byte_small_copy, short_small_copy, int_small_copy, long_small_copy;
#if INCLUDE_ZGC
    Label long_small_copy_oop, long_small_copy_oop_uninit;
#endif
    int int_oop_small_limit, long_oop_small_limit;

    if (UseLASX) {
      int_oop_small_limit = 9;
      long_oop_small_limit = 5;
      generate_disjoint_large_copy_lasx(DECORATORS_NONE, T_LONG, disjoint_large_copy, "disjoint_large_copy_lasx");
      generate_conjoint_large_copy_lasx(DECORATORS_NONE, T_LONG, conjoint_large_copy, "conjoint_large_copy_lasx");
#if INCLUDE_ZGC
      if (UseZGC) {
        generate_disjoint_large_copy_lasx(IN_HEAP | IS_ARRAY | ARRAYCOPY_DISJOINT, T_OBJECT, disjoint_large_copy_oop, "disjoint_large_copy_oop_lasx");
        generate_conjoint_large_copy_lasx(IN_HEAP | IS_ARRAY, T_OBJECT, conjoint_large_copy_oop, "conjoint_large_copy_oop_lasx");
        generate_disjoint_large_copy_lasx(IN_HEAP | IS_ARRAY | ARRAYCOPY_DISJOINT | IS_DEST_UNINITIALIZED, T_OBJECT, disjoint_large_copy_oop_uninit, "disjoint_large_copy_oop_uninit_lasx");
        generate_conjoint_large_copy_lasx(IN_HEAP | IS_ARRAY | IS_DEST_UNINITIALIZED, T_OBJECT, conjoint_large_copy_oop_uninit, "conjoint_large_copy_oop_uninit_lasx");
      }
#endif
    } else if (UseLSX) {
      int_oop_small_limit = 7;
      long_oop_small_limit = 4;
      generate_disjoint_large_copy_lsx(DECORATORS_NONE, T_LONG, disjoint_large_copy, "disjoint_large_copy_lsx");
      generate_conjoint_large_copy_lsx(DECORATORS_NONE, T_LONG, conjoint_large_copy, "conjoint_large_copy_lsx");
#if INCLUDE_ZGC
      if (UseZGC) {
        generate_disjoint_large_copy_lsx(IN_HEAP | IS_ARRAY | ARRAYCOPY_DISJOINT, T_OBJECT, disjoint_large_copy_oop, "disjoint_large_copy_oop_lsx");
        generate_conjoint_large_copy_lsx(IN_HEAP | IS_ARRAY, T_OBJECT, conjoint_large_copy_oop, "conjoint_large_copy_oop_lsx");
        generate_disjoint_large_copy_lsx(IN_HEAP | IS_ARRAY | ARRAYCOPY_DISJOINT | IS_DEST_UNINITIALIZED, T_OBJECT, disjoint_large_copy_oop_uninit, "disjoint_large_copy_oop_uninit_lsx");
        generate_conjoint_large_copy_lsx(IN_HEAP | IS_ARRAY | IS_DEST_UNINITIALIZED, T_OBJECT, conjoint_large_copy_oop_uninit, "conjoint_large_copy_oop_uninit_lsx");
      }
#endif
    } else {
      int_oop_small_limit = 7;
      long_oop_small_limit = 4;
      generate_disjoint_large_copy(DECORATORS_NONE, T_LONG, disjoint_large_copy, "disjoint_large_copy_int");
      generate_conjoint_large_copy(DECORATORS_NONE, T_LONG, conjoint_large_copy, "conjoint_large_copy_int");
#if INCLUDE_ZGC
    if (UseZGC) {
      generate_disjoint_large_copy(IN_HEAP | IS_ARRAY | ARRAYCOPY_DISJOINT, T_OBJECT, disjoint_large_copy_oop, "disjoint_large_copy_oop");
      generate_conjoint_large_copy(IN_HEAP | IS_ARRAY, T_OBJECT, conjoint_large_copy_oop, "conjoint_large_copy_oop");
      generate_disjoint_large_copy(IN_HEAP | IS_ARRAY | ARRAYCOPY_DISJOINT | IS_DEST_UNINITIALIZED, T_OBJECT, disjoint_large_copy_oop_uninit, "disjoint_large_copy_oop_uninit");
      generate_conjoint_large_copy(IN_HEAP | IS_ARRAY | IS_DEST_UNINITIALIZED, T_OBJECT, conjoint_large_copy_oop_uninit, "conjoint_large_copy_oop_uninit");
    }
#endif
    }
    generate_byte_small_copy(byte_small_copy, "jbyte_small_copy");
    generate_short_small_copy(short_small_copy, "jshort_small_copy");
    generate_int_small_copy(int_small_copy, "jint_small_copy");
    generate_long_small_copy(DECORATORS_NONE, T_LONG, long_small_copy, "jlong_small_copy");
#if INCLUDE_ZGC
    if (UseZGC) {
      generate_long_small_copy(IN_HEAP | IS_ARRAY | ARRAYCOPY_DISJOINT, T_OBJECT, long_small_copy_oop, "jlong_small_copy_oop");
      generate_long_small_copy(IN_HEAP | IS_ARRAY | ARRAYCOPY_DISJOINT | IS_DEST_UNINITIALIZED, T_OBJECT, long_small_copy_oop_uninit, "jlong_small_copy_oop_uninit");
    }
#endif

    if (UseCompressedOops) {
      StubRoutines::_oop_disjoint_arraycopy        = generate_disjoint_int_oop_copy(false, true, int_small_copy, disjoint_large_copy,
                                                                                    "oop_disjoint_arraycopy", int_oop_small_limit);
      StubRoutines::_oop_disjoint_arraycopy_uninit = generate_disjoint_int_oop_copy(false, true, int_small_copy, disjoint_large_copy,
                                                                                    "oop_disjoint_arraycopy_uninit", int_oop_small_limit, true);
      StubRoutines::_oop_arraycopy                 = generate_conjoint_int_oop_copy(false, true, int_small_copy, conjoint_large_copy,
                                                                                    "oop_arraycopy", int_oop_small_limit);
      StubRoutines::_oop_arraycopy_uninit          = generate_conjoint_int_oop_copy(false, true, int_small_copy, conjoint_large_copy,
                                                                                    "oop_arraycopy_uninit", int_oop_small_limit, true);
    } else {
#if INCLUDE_ZGC
      if (UseZGC) {
        StubRoutines::_oop_disjoint_arraycopy        = generate_disjoint_long_oop_copy(false, true, long_small_copy_oop, disjoint_large_copy_oop,
                                                                                       "oop_disjoint_arraycopy", long_oop_small_limit);
        StubRoutines::_oop_disjoint_arraycopy_uninit = generate_disjoint_long_oop_copy(false, true, long_small_copy_oop_uninit, disjoint_large_copy_oop_uninit,
                                                                                       "oop_disjoint_arraycopy_uninit", long_oop_small_limit, true);
        StubRoutines::_oop_arraycopy                 = generate_conjoint_long_oop_copy(false, true, long_small_copy_oop, conjoint_large_copy_oop,
                                                                                       "oop_arraycopy", long_oop_small_limit);
        StubRoutines::_oop_arraycopy_uninit          = generate_conjoint_long_oop_copy(false, true, long_small_copy_oop_uninit, conjoint_large_copy_oop_uninit,
                                                                                       "oop_arraycopy_uninit", long_oop_small_limit, true);
      } else {
#endif
        StubRoutines::_oop_disjoint_arraycopy        = generate_disjoint_long_oop_copy(false, true, long_small_copy, disjoint_large_copy,
                                                                                       "oop_disjoint_arraycopy", long_oop_small_limit);
        StubRoutines::_oop_disjoint_arraycopy_uninit = generate_disjoint_long_oop_copy(false, true, long_small_copy, disjoint_large_copy,
                                                                                       "oop_disjoint_arraycopy_uninit", long_oop_small_limit, true);
        StubRoutines::_oop_arraycopy                 = generate_conjoint_long_oop_copy(false, true, long_small_copy, conjoint_large_copy,
                                                                                       "oop_arraycopy", long_oop_small_limit);
        StubRoutines::_oop_arraycopy_uninit          = generate_conjoint_long_oop_copy(false, true, long_small_copy, conjoint_large_copy,
                                                                                       "oop_arraycopy_uninit", long_oop_small_limit, true);
#if INCLUDE_ZGC
      }
#endif
    }

    StubRoutines::_jbyte_disjoint_arraycopy        = generate_disjoint_byte_copy(false, byte_small_copy, disjoint_large_copy, "jbyte_disjoint_arraycopy");
    StubRoutines::_jshort_disjoint_arraycopy       = generate_disjoint_short_copy(false, short_small_copy, disjoint_large_copy, "jshort_disjoint_arraycopy");
    StubRoutines::_jint_disjoint_arraycopy         = generate_disjoint_int_oop_copy(false, false, int_small_copy, disjoint_large_copy,
                                                                                    "jint_disjoint_arraycopy", int_oop_small_limit);

    StubRoutines::_jbyte_arraycopy                 = generate_conjoint_byte_copy(false, byte_small_copy, conjoint_large_copy, "jbyte_arraycopy");
    StubRoutines::_jshort_arraycopy                = generate_conjoint_short_copy(false, short_small_copy, conjoint_large_copy, "jshort_arraycopy");
    StubRoutines::_jint_arraycopy                  = generate_conjoint_int_oop_copy(false, false, int_small_copy, conjoint_large_copy,
                                                                                    "jint_arraycopy", int_oop_small_limit);

    StubRoutines::_jlong_disjoint_arraycopy        = generate_disjoint_long_oop_copy(false, false, long_small_copy, disjoint_large_copy,
                                                                                     "jlong_disjoint_arraycopy", long_oop_small_limit);
    StubRoutines::_jlong_arraycopy                 = generate_conjoint_long_oop_copy(false, false, long_small_copy, conjoint_large_copy,
                                                                                     "jlong_arraycopy", long_oop_small_limit);

    // We don't generate specialized code for HeapWord-aligned source
    // arrays, so just use the code we've already generated
    StubRoutines::_arrayof_jbyte_disjoint_arraycopy  = StubRoutines::_jbyte_disjoint_arraycopy;
    StubRoutines::_arrayof_jbyte_arraycopy           = StubRoutines::_jbyte_arraycopy;

    StubRoutines::_arrayof_jshort_disjoint_arraycopy = StubRoutines::_jshort_disjoint_arraycopy;
    StubRoutines::_arrayof_jshort_arraycopy          = StubRoutines::_jshort_arraycopy;

    StubRoutines::_arrayof_jint_disjoint_arraycopy   = StubRoutines::_jint_disjoint_arraycopy;
    StubRoutines::_arrayof_jint_arraycopy            = StubRoutines::_jint_arraycopy;

    StubRoutines::_arrayof_jlong_disjoint_arraycopy  = StubRoutines::_jlong_disjoint_arraycopy;
    StubRoutines::_arrayof_jlong_arraycopy           = StubRoutines::_jlong_arraycopy;

    StubRoutines::_arrayof_oop_disjoint_arraycopy    = StubRoutines::_oop_disjoint_arraycopy;
    StubRoutines::_arrayof_oop_arraycopy             = StubRoutines::_oop_arraycopy;

    StubRoutines::_arrayof_oop_disjoint_arraycopy_uninit    = StubRoutines::_oop_disjoint_arraycopy_uninit;
    StubRoutines::_arrayof_oop_arraycopy_uninit             = StubRoutines::_oop_arraycopy_uninit;

    StubRoutines::_checkcast_arraycopy        = generate_checkcast_copy("checkcast_arraycopy");
    StubRoutines::_checkcast_arraycopy_uninit = generate_checkcast_copy("checkcast_arraycopy_uninit", true);

    StubRoutines::_unsafe_arraycopy = generate_unsafe_copy("unsafe_arraycopy");

    StubRoutines::_generic_arraycopy = generate_generic_copy("generic_arraycopy");

    StubRoutines::_jbyte_fill = generate_fill(T_BYTE, false, "jbyte_fill");
    StubRoutines::_jshort_fill = generate_fill(T_SHORT, false, "jshort_fill");
    StubRoutines::_jint_fill = generate_fill(T_INT, false, "jint_fill");
    StubRoutines::_arrayof_jbyte_fill = generate_fill(T_BYTE, true, "arrayof_jbyte_fill");
    StubRoutines::_arrayof_jshort_fill = generate_fill(T_SHORT, true, "arrayof_jshort_fill");
    StubRoutines::_arrayof_jint_fill = generate_fill(T_INT, true, "arrayof_jint_fill");

    StubRoutines::la::_jlong_fill = generate_fill(T_LONG, false, "jlong_fill");
    StubRoutines::la::_arrayof_jlong_fill = generate_fill(T_LONG, true, "arrayof_jlong_fill");

#if INCLUDE_ZGC
    if (!UseZGC) {
#endif
      Copy::_conjoint_words = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::jlong_arraycopy());
      Copy::_disjoint_words = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::jlong_disjoint_arraycopy());
      Copy::_disjoint_words_atomic = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::jlong_disjoint_arraycopy());
      Copy::_aligned_conjoint_words = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::jlong_arraycopy());
      Copy::_aligned_disjoint_words = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::jlong_disjoint_arraycopy());
      Copy::_conjoint_bytes = reinterpret_cast<Copy::CopyByte>(StubRoutines::jbyte_arraycopy());
      Copy::_conjoint_bytes_atomic = reinterpret_cast<Copy::CopyByte>(StubRoutines::jbyte_arraycopy());
      Copy::_conjoint_jshorts_atomic = reinterpret_cast<Copy::CopyShort>(StubRoutines::jshort_arraycopy());
      Copy::_conjoint_jints_atomic = reinterpret_cast<Copy::CopyInt>(StubRoutines::jint_arraycopy());
      Copy::_conjoint_jlongs_atomic = reinterpret_cast<Copy::CopyLong>(StubRoutines::jlong_arraycopy());
      Copy::_conjoint_oops_atomic = reinterpret_cast<Copy::CopyOop>(StubRoutines::jlong_arraycopy());
      Copy::_arrayof_conjoint_bytes = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::arrayof_jbyte_arraycopy());
      Copy::_arrayof_conjoint_jshorts = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::arrayof_jshort_arraycopy());
      Copy::_arrayof_conjoint_jints = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::arrayof_jint_arraycopy());
      Copy::_arrayof_conjoint_jlongs = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::arrayof_jlong_arraycopy());
      Copy::_arrayof_conjoint_oops = reinterpret_cast<Copy::CopyHeapWord>(StubRoutines::arrayof_jlong_arraycopy());
      Copy::_fill_to_bytes = reinterpret_cast<Copy::FillByte>(StubRoutines::jbyte_fill());
      Copy::_fill_to_words = reinterpret_cast<Copy::FillHeapWord>(StubRoutines::la::jlong_fill());
      Copy::_fill_to_aligned_words = reinterpret_cast<Copy::FillHeapWord>(StubRoutines::la::arrayof_jlong_fill());;
#if INCLUDE_ZGC
    }
#endif
  }

  address generate_method_entry_barrier() {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "nmethod_entry_barrier");

    Label deoptimize_label;
    Register rscratch2 = T8;

    address start = __ pc();

    BarrierSetAssembler* bs_asm = BarrierSet::barrier_set()->barrier_set_assembler();

    if (bs_asm->nmethod_patching_type() == NMethodPatchingType::conc_instruction_and_data_patch) {
      BarrierSetNMethod* bs_nm = BarrierSet::barrier_set()->barrier_set_nmethod();
      Address thread_epoch_addr(TREG, in_bytes(bs_nm->thread_disarmed_guard_value_offset()) + 4);
      __ lea_long(SCR1, ExternalAddress(bs_asm->patching_epoch_addr()));
      __ ld_wu(SCR1, SCR1, 0);
      __ st_w(SCR1, thread_epoch_addr);
      __ ibar(0);
      __ membar(__ LoadLoad);
    }

    __ set_last_Java_frame(SP, FP, RA);

    __ enter();
    __ addi_d(T4, SP, wordSize);  // T4 points to the saved RA

    __ addi_d(SP, SP, -4 * wordSize);  // four words for the returned {SP, FP, RA, PC}

    __ push(V0);
    __ push_call_clobbered_registers_except(RegSet::of(V0));

    __ move(A0, T4);
    __ call_VM_leaf
         (CAST_FROM_FN_PTR
          (address, BarrierSetNMethod::nmethod_stub_entry_barrier), 1);

    __ reset_last_Java_frame(true);

    __ pop_call_clobbered_registers_except(RegSet::of(V0));

    __ bnez(V0, deoptimize_label);

    __ pop(V0);
    __ leave();
    __ jr(RA);

    __ bind(deoptimize_label);

    __ pop(V0);
    __ ld_d(rscratch2, SP, 0);
    __ ld_d(FP, SP, 1 * wordSize);
    __ ld_d(RA, SP, 2 * wordSize);
    __ ld_d(T4, SP, 3 * wordSize);

    __ move(SP, rscratch2);
    __ jr(T4);

    return start;
  }

  // T8 result
  // A4 src
  // A5 src count
  // A6 pattern
  // A7 pattern count
  address generate_string_indexof_linear(bool needle_isL, bool haystack_isL)
  {
    const char* stubName = needle_isL
           ? (haystack_isL ? "indexof_linear_ll" : "indexof_linear_ul")
           : "indexof_linear_uu";
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", stubName);
    address entry = __ pc();

    int needle_chr_size = needle_isL ? 1 : 2;
    int haystack_chr_size = haystack_isL ? 1 : 2;
    int needle_chr_shift = needle_isL ? 0 : 1;
    int haystack_chr_shift = haystack_isL ? 0 : 1;
    bool isL = needle_isL && haystack_isL;

    // parameters
    Register result = T8, haystack = A4, haystack_len = A5, needle = A6, needle_len = A7;

    // temporary registers
    Register match_mask = T0, mask1 = T1, mask2 = T2;
    Register first = T3, trailing_zeros = T4;
    Register ch1 = T5, ch2 = T6;

    RegSet spilled_regs = RegSet::range(T0, T6);

    __ push(spilled_regs);

    Label L_LOOP, L_LOOP_PROCEED, L_SMALL, L_HAS_ZERO, L_SMALL_HAS_ZERO,
          L_HAS_ZERO_LOOP, L_CMP_LOOP, L_CMP_LOOP_NOMATCH,
          L_SMALL_HAS_ZERO_LOOP, L_SMALL_CMP_LOOP_NOMATCH, L_SMALL_CMP_LOOP,
          L_POST_LOOP, L_CMP_LOOP_LAST_CMP, L_HAS_ZERO_LOOP_NOMATCH,
          L_SMALL_CMP_LOOP_LAST_CMP, L_SMALL_CMP_LOOP_LAST_CMP2,
          L_CMP_LOOP_LAST_CMP2, DONE, NOMATCH;

    __ ld_d(ch1, Address(needle));

    // src.length - pattern.length
    __ sub_d(haystack_len, haystack_len, needle_len);

    // first is needle[0]
    __ bstrpick_d(first, ch1, needle_isL ? 7 : 15, 0);

    uint64_t mask0101 = UCONST64(0x0101010101010101);
    uint64_t mask0001 = UCONST64(0x0001000100010001);
    __ li(mask1, haystack_isL ? mask0101 : mask0001);

    uint64_t mask7f7f = UCONST64(0x7f7f7f7f7f7f7f7f);
    uint64_t mask7fff = UCONST64(0x7fff7fff7fff7fff);
    __ li(mask2, haystack_isL ? mask7f7f : mask7fff);

    // first -> needle[0]needle[0]needle[0]needle[0]
    if (haystack_isL) __ bstrins_d(first, first, 15, 8);
    __ bstrins_d(first, first, 31, 16);
    __ bstrins_d(first, first, 63, 32);

    if (needle_isL != haystack_isL) {
      // convert Latin1 to UTF. eg: 0x0000abcd -> 0x0a0b0c0d
      __ move(AT, ch1);
      __ bstrpick_d(ch1, AT, 7, 0);
      __ srli_d(AT, AT, 8);
      __ bstrins_d(ch1, AT, 23, 16);
      __ srli_d(AT, AT, 8);
      __ bstrins_d(ch1, AT, 39, 32);
      __ srli_d(AT, AT, 8);
      __ bstrins_d(ch1, AT, 55, 48);
    }

    __ addi_d(haystack_len, haystack_len, -1 * (wordSize / haystack_chr_size - 1));
    __ bge(R0, haystack_len, L_SMALL);

    // compare and set match_mask[i] with 0x80/0x8000 (Latin1/UTF16) if ch2[i] == first[i]
    // eg:
    // first:        aa aa aa aa aa aa aa aa
    // ch2:          aa aa li nx jd ka aa aa
    // match_mask:   80 80 00 00 00 00 80 80

    __ bind(L_LOOP);
    __ ld_d(ch2, Address(haystack));
    // compute match_mask
    __ xorr(ch2, first, ch2);
    __ sub_d(match_mask, ch2, mask1);
    __ orr(ch2, ch2, mask2);
    __ andn(match_mask, match_mask, ch2);
    // search first char of needle, goto L_HAS_ZERO if success.
    __ bnez(match_mask, L_HAS_ZERO);

    __ bind(L_LOOP_PROCEED);
    __ addi_d(haystack_len, haystack_len, -1 * (wordSize / haystack_chr_size));
    __ addi_d(haystack, haystack, wordSize);
    __ addi_d(result, result, wordSize / haystack_chr_size);
    __ bge(haystack_len, R0, L_LOOP);

    __ bind(L_POST_LOOP);
    __ li(ch2, -1 * (wordSize / haystack_chr_size));
    __ bge(ch2, haystack_len, NOMATCH); // no extra characters to check

    __ bind(L_SMALL);
    __ ld_d(ch2, Address(haystack));
    __ slli_d(haystack_len, haystack_len, LogBitsPerByte + haystack_chr_shift);
    __ sub_d(haystack_len, R0, haystack_len);
    // compute match_mask
    __ xorr(ch2, first, ch2);
    __ sub_d(match_mask, ch2, mask1);
    __ orr(ch2, ch2, mask2);
    __ andn(match_mask, match_mask, ch2);
    // clear useless match_mask bits and check
    __ nor(trailing_zeros, R0, R0); // all bits set
    __ srl_d(trailing_zeros, trailing_zeros, haystack_len); // zeroes on useless bits.
    __ andr(match_mask, match_mask, trailing_zeros); // refine match_mask
    __ beqz(match_mask, NOMATCH);

    __ bind(L_SMALL_HAS_ZERO);
    __ ctz_d(trailing_zeros, match_mask);
    __ li(AT, wordSize / haystack_chr_size);
    __ bge(AT, needle_len, L_SMALL_CMP_LOOP_LAST_CMP2);

    __ bind(L_SMALL_HAS_ZERO_LOOP);
    // compute index
    __ srl_d(match_mask, match_mask, trailing_zeros);
    __ srli_d(match_mask, match_mask, 1);
    __ srli_d(AT, trailing_zeros, LogBitsPerByte);
    if (!haystack_isL) __ andi(AT, AT, 0xE);
    __ add_d(haystack, haystack, AT);
    __ ld_d(ch2, Address(haystack));
    if (!haystack_isL) __ srli_d(AT, AT, haystack_chr_shift);
    __ add_d(result, result, AT);

    __ li(trailing_zeros, wordSize / haystack_chr_size);
    __ bne(ch1, ch2, L_SMALL_CMP_LOOP_NOMATCH);

    __ bind(L_SMALL_CMP_LOOP);
    needle_isL ? __ ld_bu(first, Address(needle, trailing_zeros, Address::no_scale, 0))
               : __ ld_hu(first, Address(needle, trailing_zeros, Address::times_2, 0));
    haystack_isL ? __ ld_bu(ch2, Address(haystack, trailing_zeros, Address::no_scale, 0))
                 : __ ld_hu(ch2, Address(haystack, trailing_zeros, Address::times_2, 0));
    __ addi_d(trailing_zeros, trailing_zeros, 1);
    __ bge(trailing_zeros, needle_len, L_SMALL_CMP_LOOP_LAST_CMP);
    __ beq(first, ch2, L_SMALL_CMP_LOOP);

    __ bind(L_SMALL_CMP_LOOP_NOMATCH);
    __ beqz(match_mask, NOMATCH);
    __ ctz_d(trailing_zeros, match_mask);
    __ addi_d(result, result, 1);
    __ addi_d(haystack, haystack, haystack_chr_size);
    __ b(L_SMALL_HAS_ZERO_LOOP);

    __ bind(L_SMALL_CMP_LOOP_LAST_CMP);
    __ bne(first, ch2, L_SMALL_CMP_LOOP_NOMATCH);
    __ b(DONE);

    __ bind(L_SMALL_CMP_LOOP_LAST_CMP2);
    // compute index
    __ srl_d(match_mask, match_mask, trailing_zeros);
    __ srli_d(match_mask, match_mask, 1);
    __ srli_d(AT, trailing_zeros, LogBitsPerByte);
    if (!haystack_isL) __ andi(AT, AT, 0xE);
    __ add_d(haystack, haystack, AT);
    __ ld_d(ch2, Address(haystack));
    if (!haystack_isL) __ srli_d(AT, AT, haystack_chr_shift);
    __ add_d(result, result, AT);

    __ bne(ch1, ch2, L_SMALL_CMP_LOOP_NOMATCH);
    __ b(DONE);

    __ bind(L_HAS_ZERO);
    __ ctz_d(trailing_zeros, match_mask);
    __ li(AT, wordSize / haystack_chr_size);
    __ bge(AT, needle_len, L_CMP_LOOP_LAST_CMP2);
    __ addi_d(result, result, -1); // array index from 0, so result -= 1

    __ bind(L_HAS_ZERO_LOOP);
    // compute index
    __ srl_d(match_mask, match_mask, trailing_zeros);
    __ srli_d(match_mask, match_mask, 1);
    __ srli_d(AT, trailing_zeros, LogBitsPerByte);
    if (!haystack_isL) __ andi(AT, AT, 0xE);
    __ add_d(haystack, haystack, AT);
    __ ld_d(ch2, Address(haystack));
    if (!haystack_isL) __ srli_d(AT, AT, haystack_chr_shift);
    __ add_d(result, result, AT);

    __ addi_d(result, result, 1);
    __ li(trailing_zeros, wordSize / haystack_chr_size);
    __ bne(ch1, ch2, L_CMP_LOOP_NOMATCH);

    // compare one char
    __ bind(L_CMP_LOOP);
    haystack_isL ? __ ld_bu(ch2, Address(haystack, trailing_zeros, Address::no_scale, 0))
                 : __ ld_hu(ch2, Address(haystack, trailing_zeros, Address::times_2, 0));
    needle_isL ? __ ld_bu(AT, Address(needle, trailing_zeros, Address::no_scale, 0))
               : __ ld_hu(AT, Address(needle, trailing_zeros, Address::times_2, 0));
    __ addi_d(trailing_zeros, trailing_zeros, 1); // next char index
    __ bge(trailing_zeros, needle_len, L_CMP_LOOP_LAST_CMP);
    __ beq(AT, ch2, L_CMP_LOOP);

    __ bind(L_CMP_LOOP_NOMATCH);
    __ beqz(match_mask, L_HAS_ZERO_LOOP_NOMATCH);
    __ ctz_d(trailing_zeros, match_mask);
    __ addi_d(haystack, haystack, haystack_chr_size);
    __ b(L_HAS_ZERO_LOOP);

    __ bind(L_CMP_LOOP_LAST_CMP);
    __ bne(AT, ch2, L_CMP_LOOP_NOMATCH);
    __ b(DONE);

    __ bind(L_CMP_LOOP_LAST_CMP2);
    // compute index
    __ srl_d(match_mask, match_mask, trailing_zeros);
    __ srli_d(match_mask, match_mask, 1);
    __ srli_d(AT, trailing_zeros, LogBitsPerByte);
    if (!haystack_isL) __ andi(AT, AT, 0xE);
    __ add_d(haystack, haystack, AT);
    __ ld_d(ch2, Address(haystack));
    if (!haystack_isL) __ srli_d(AT, AT, haystack_chr_shift);
    __ add_d(result, result, AT);

    __ addi_d(result, result, 1);
    __ bne(ch1, ch2, L_CMP_LOOP_NOMATCH);
    __ b(DONE);

    __ bind(L_HAS_ZERO_LOOP_NOMATCH);
    // 1) Restore "result" index. Index was wordSize/str2_chr_size * N until
    // L_HAS_ZERO block. Byte octet was analyzed in L_HAS_ZERO_LOOP,
    // so, result was increased at max by wordSize/str2_chr_size - 1, so,
    // respective high bit wasn't changed. L_LOOP_PROCEED will increase
    // result by analyzed characters value, so, we can just reset lower bits
    // in result here. Clear 2 lower bits for UU/UL and 3 bits for LL
    // 2) advance haystack value to represent next haystack octet. result & 7/3 is
    // index of last analyzed substring inside current octet. So, haystack in at
    // respective start address. We need to advance it to next octet
    __ andi(match_mask, result, wordSize / haystack_chr_size - 1);
    __ sub_d(result, result, match_mask);
    if (!haystack_isL) __ slli_d(match_mask, match_mask, haystack_chr_shift);
    __ sub_d(haystack, haystack, match_mask);
    __ b(L_LOOP_PROCEED);

    __ bind(NOMATCH);
    __ nor(result, R0, R0); // result = -1

    __ bind(DONE);
    __ pop(spilled_regs);
    __ jr(RA);
    return entry;
  }

  void generate_string_indexof_stubs()
  {
    StubRoutines::la::_string_indexof_linear_ll = generate_string_indexof_linear(true, true);
    StubRoutines::la::_string_indexof_linear_uu = generate_string_indexof_linear(false, false);
    StubRoutines::la::_string_indexof_linear_ul = generate_string_indexof_linear(true, false);
  }

  address generate_mulAdd() {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "mulAdd");

    address entry = __ pc();

    const Register out     = c_rarg0;
    const Register in      = c_rarg1;
    const Register offset  = c_rarg2;
    const Register len     = c_rarg3;
    const Register k       = c_rarg4;

    __ block_comment("Entry:");
    __ mul_add(out, in, offset, len, k);
    __ jr(RA);

    return entry;
  }

  // Arguments:
  //
  // Inputs:
  //   A0        - source byte array address
  //   A1        - destination byte array address
  //   A2        - K (key) in little endian int array
  //   A3        - r vector byte array address
  //   A4        - input length
  //
  // Output:
  //   A0        - input length
  //
  address generate_aescrypt_encryptBlock(bool cbc) {
    static const uint32_t ft_consts[256] = {
      0xc66363a5, 0xf87c7c84, 0xee777799, 0xf67b7b8d,
      0xfff2f20d, 0xd66b6bbd, 0xde6f6fb1, 0x91c5c554,
      0x60303050, 0x02010103, 0xce6767a9, 0x562b2b7d,
      0xe7fefe19, 0xb5d7d762, 0x4dababe6, 0xec76769a,
      0x8fcaca45, 0x1f82829d, 0x89c9c940, 0xfa7d7d87,
      0xeffafa15, 0xb25959eb, 0x8e4747c9, 0xfbf0f00b,
      0x41adadec, 0xb3d4d467, 0x5fa2a2fd, 0x45afafea,
      0x239c9cbf, 0x53a4a4f7, 0xe4727296, 0x9bc0c05b,
      0x75b7b7c2, 0xe1fdfd1c, 0x3d9393ae, 0x4c26266a,
      0x6c36365a, 0x7e3f3f41, 0xf5f7f702, 0x83cccc4f,
      0x6834345c, 0x51a5a5f4, 0xd1e5e534, 0xf9f1f108,
      0xe2717193, 0xabd8d873, 0x62313153, 0x2a15153f,
      0x0804040c, 0x95c7c752, 0x46232365, 0x9dc3c35e,
      0x30181828, 0x379696a1, 0x0a05050f, 0x2f9a9ab5,
      0x0e070709, 0x24121236, 0x1b80809b, 0xdfe2e23d,
      0xcdebeb26, 0x4e272769, 0x7fb2b2cd, 0xea75759f,
      0x1209091b, 0x1d83839e, 0x582c2c74, 0x341a1a2e,
      0x361b1b2d, 0xdc6e6eb2, 0xb45a5aee, 0x5ba0a0fb,
      0xa45252f6, 0x763b3b4d, 0xb7d6d661, 0x7db3b3ce,
      0x5229297b, 0xdde3e33e, 0x5e2f2f71, 0x13848497,
      0xa65353f5, 0xb9d1d168, 0x00000000, 0xc1eded2c,
      0x40202060, 0xe3fcfc1f, 0x79b1b1c8, 0xb65b5bed,
      0xd46a6abe, 0x8dcbcb46, 0x67bebed9, 0x7239394b,
      0x944a4ade, 0x984c4cd4, 0xb05858e8, 0x85cfcf4a,
      0xbbd0d06b, 0xc5efef2a, 0x4faaaae5, 0xedfbfb16,
      0x864343c5, 0x9a4d4dd7, 0x66333355, 0x11858594,
      0x8a4545cf, 0xe9f9f910, 0x04020206, 0xfe7f7f81,
      0xa05050f0, 0x783c3c44, 0x259f9fba, 0x4ba8a8e3,
      0xa25151f3, 0x5da3a3fe, 0x804040c0, 0x058f8f8a,
      0x3f9292ad, 0x219d9dbc, 0x70383848, 0xf1f5f504,
      0x63bcbcdf, 0x77b6b6c1, 0xafdada75, 0x42212163,
      0x20101030, 0xe5ffff1a, 0xfdf3f30e, 0xbfd2d26d,
      0x81cdcd4c, 0x180c0c14, 0x26131335, 0xc3ecec2f,
      0xbe5f5fe1, 0x359797a2, 0x884444cc, 0x2e171739,
      0x93c4c457, 0x55a7a7f2, 0xfc7e7e82, 0x7a3d3d47,
      0xc86464ac, 0xba5d5de7, 0x3219192b, 0xe6737395,
      0xc06060a0, 0x19818198, 0x9e4f4fd1, 0xa3dcdc7f,
      0x44222266, 0x542a2a7e, 0x3b9090ab, 0x0b888883,
      0x8c4646ca, 0xc7eeee29, 0x6bb8b8d3, 0x2814143c,
      0xa7dede79, 0xbc5e5ee2, 0x160b0b1d, 0xaddbdb76,
      0xdbe0e03b, 0x64323256, 0x743a3a4e, 0x140a0a1e,
      0x924949db, 0x0c06060a, 0x4824246c, 0xb85c5ce4,
      0x9fc2c25d, 0xbdd3d36e, 0x43acacef, 0xc46262a6,
      0x399191a8, 0x319595a4, 0xd3e4e437, 0xf279798b,
      0xd5e7e732, 0x8bc8c843, 0x6e373759, 0xda6d6db7,
      0x018d8d8c, 0xb1d5d564, 0x9c4e4ed2, 0x49a9a9e0,
      0xd86c6cb4, 0xac5656fa, 0xf3f4f407, 0xcfeaea25,
      0xca6565af, 0xf47a7a8e, 0x47aeaee9, 0x10080818,
      0x6fbabad5, 0xf0787888, 0x4a25256f, 0x5c2e2e72,
      0x381c1c24, 0x57a6a6f1, 0x73b4b4c7, 0x97c6c651,
      0xcbe8e823, 0xa1dddd7c, 0xe874749c, 0x3e1f1f21,
      0x964b4bdd, 0x61bdbddc, 0x0d8b8b86, 0x0f8a8a85,
      0xe0707090, 0x7c3e3e42, 0x71b5b5c4, 0xcc6666aa,
      0x904848d8, 0x06030305, 0xf7f6f601, 0x1c0e0e12,
      0xc26161a3, 0x6a35355f, 0xae5757f9, 0x69b9b9d0,
      0x17868691, 0x99c1c158, 0x3a1d1d27, 0x279e9eb9,
      0xd9e1e138, 0xebf8f813, 0x2b9898b3, 0x22111133,
      0xd26969bb, 0xa9d9d970, 0x078e8e89, 0x339494a7,
      0x2d9b9bb6, 0x3c1e1e22, 0x15878792, 0xc9e9e920,
      0x87cece49, 0xaa5555ff, 0x50282878, 0xa5dfdf7a,
      0x038c8c8f, 0x59a1a1f8, 0x09898980, 0x1a0d0d17,
      0x65bfbfda, 0xd7e6e631, 0x844242c6, 0xd06868b8,
      0x824141c3, 0x299999b0, 0x5a2d2d77, 0x1e0f0f11,
      0x7bb0b0cb, 0xa85454fc, 0x6dbbbbd6, 0x2c16163a
    };
    static const uint8_t fsb_consts[256] = {
      0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5,
      0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
      0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0,
      0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
      0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc,
      0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
      0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a,
      0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
      0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0,
      0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
      0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b,
      0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
      0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85,
      0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
      0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5,
      0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
      0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17,
      0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
      0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88,
      0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
      0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c,
      0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
      0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9,
      0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
      0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6,
      0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
      0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e,
      0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
      0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94,
      0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
      0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68,
      0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
    };

    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "aescrypt_encryptBlock");

    // Allocate registers
    Register src = A0;
    Register dst = A1;
    Register key = A2;
    Register rve = A3;
    Register srclen = A4;
    Register keylen = T8;
    Register srcend = A5;
    Register keyold = A6;
    Register t0 = A7;
    Register t1, t2, t3, ftp;
    Register xa[4] = { T0, T1, T2, T3 };
    Register ya[4] = { T4, T5, T6, T7 };

    Label loop, tail, done;
    address start = __ pc();

    if (cbc) {
      t1 = S0;
      t2 = S1;
      t3 = S2;
      ftp = S3;

      __ beqz(srclen, done);

      __ addi_d(SP, SP, -4 * wordSize);
      __ st_d(S3, SP, 3 * wordSize);
      __ st_d(S2, SP, 2 * wordSize);
      __ st_d(S1, SP, 1 * wordSize);
      __ st_d(S0, SP, 0 * wordSize);

      __ add_d(srcend, src, srclen);
      __ move(keyold, key);
    } else {
      t1 = A3;
      t2 = A4;
      t3 = A5;
      ftp = A6;
    }

    __ ld_w(keylen, key, arrayOopDesc::length_offset_in_bytes() - arrayOopDesc::base_offset_in_bytes(T_INT));

    // Round 1
    if (cbc) {
      for (int i = 0; i < 4; i++) {
        __ ld_w(xa[i], rve, 4 * i);
      }

      __ bind(loop);

      for (int i = 0; i < 4; i++) {
        __ ld_w(ya[i], src, 4 * i);
      }
      for (int i = 0; i < 4; i++) {
        __ XOR(xa[i], xa[i], ya[i]);
      }
    } else {
      for (int i = 0; i < 4; i++) {
        __ ld_w(xa[i], src, 4 * i);
      }
    }
    for (int i = 0; i < 4; i++) {
      __ ld_w(ya[i], key, 4 * i);
    }
    for (int i = 0; i < 4; i++) {
      __ revb_2h(xa[i], xa[i]);
    }
    for (int i = 0; i < 4; i++) {
      __ rotri_w(xa[i], xa[i], 16);
    }
    for (int i = 0; i < 4; i++) {
      __ XOR(xa[i], xa[i], ya[i]);
    }

    __ li(ftp, (intptr_t)ft_consts);

    // Round 2 - (N-1)
    for (int r = 0; r < 14; r++) {
      Register *xp;
      Register *yp;

      if (r & 1) {
        xp = xa;
        yp = ya;
      } else {
        xp = ya;
        yp = xa;
      }

      for (int i = 0; i < 4; i++) {
        __ ld_w(xp[i], key, 4 * (4 * (r + 1) + i));
      }

      for (int i = 0; i < 4; i++) {
        __ bstrpick_d(t0, yp[(i + 3) & 3], 7, 0);
        __ bstrpick_d(t1, yp[(i + 2) & 3], 15, 8);
        __ bstrpick_d(t2, yp[(i + 1) & 3], 23, 16);
        __ bstrpick_d(t3, yp[(i + 0) & 3], 31, 24);
        __ slli_w(t0, t0, 2);
        __ slli_w(t1, t1, 2);
        __ slli_w(t2, t2, 2);
        __ slli_w(t3, t3, 2);
        __ ldx_w(t0, ftp, t0);
        __ ldx_w(t1, ftp, t1);
        __ ldx_w(t2, ftp, t2);
        __ ldx_w(t3, ftp, t3);
        __ rotri_w(t0, t0, 24);
        __ rotri_w(t1, t1, 16);
        __ rotri_w(t2, t2, 8);
        __ XOR(xp[i], xp[i], t0);
        __ XOR(t0, t1, t2);
        __ XOR(xp[i], xp[i], t3);
        __ XOR(xp[i], xp[i], t0);
      }

      if (r == 8) {
        // AES 128
        __ li(t0, 44);
        __ beq(t0, keylen, tail);
      } else if (r == 10) {
        // AES 192
        __ li(t0, 52);
        __ beq(t0, keylen, tail);
      }
    }

    __ bind(tail);
    __ li(ftp, (intptr_t)fsb_consts);
    __ alsl_d(key, keylen, key, 2 - 1);

    // Round N
    for (int i = 0; i < 4; i++) {
      __ bstrpick_d(t0, ya[(i + 3) & 3], 7, 0);
      __ bstrpick_d(t1, ya[(i + 2) & 3], 15, 8);
      __ bstrpick_d(t2, ya[(i + 1) & 3], 23, 16);
      __ bstrpick_d(t3, ya[(i + 0) & 3], 31, 24);
      __ ldx_bu(t0, ftp, t0);
      __ ldx_bu(t1, ftp, t1);
      __ ldx_bu(t2, ftp, t2);
      __ ldx_bu(t3, ftp, t3);
      __ ld_w(xa[i], key, 4 * i - 16);
      __ slli_w(t1, t1, 8);
      __ slli_w(t2, t2, 16);
      __ slli_w(t3, t3, 24);
      __ XOR(xa[i], xa[i], t0);
      __ XOR(t0, t1, t2);
      __ XOR(xa[i], xa[i], t3);
      __ XOR(xa[i], xa[i], t0);
    }

    for (int i = 0; i < 4; i++) {
      __ revb_2h(xa[i], xa[i]);
    }
    for (int i = 0; i < 4; i++) {
      __ rotri_w(xa[i], xa[i], 16);
    }
    for (int i = 0; i < 4; i++) {
      __ st_w(xa[i], dst, 4 * i);
    }

    if (cbc) {
      __ move(key, keyold);
      __ addi_d(src, src, 16);
      __ addi_d(dst, dst, 16);
      __ blt(src, srcend, loop);

      for (int i = 0; i < 4; i++) {
        __ st_w(xa[i], rve, 4 * i);
      }

      __ ld_d(S3, SP, 3 * wordSize);
      __ ld_d(S2, SP, 2 * wordSize);
      __ ld_d(S1, SP, 1 * wordSize);
      __ ld_d(S0, SP, 0 * wordSize);
      __ addi_d(SP, SP, 4 * wordSize);

      __ bind(done);
      __ move(A0, srclen);
    }

    __ jr(RA);

    return start;
  }

  // Arguments:
  //
  // Inputs:
  //   A0        - source byte array address
  //   A1        - destination byte array address
  //   A2        - K (key) in little endian int array
  //   A3        - r vector byte array address
  //   A4        - input length
  //
  // Output:
  //   A0        - input length
  //
  address generate_aescrypt_decryptBlock(bool cbc) {
    static const uint32_t rt_consts[256] = {
      0x51f4a750, 0x7e416553, 0x1a17a4c3, 0x3a275e96,
      0x3bab6bcb, 0x1f9d45f1, 0xacfa58ab, 0x4be30393,
      0x2030fa55, 0xad766df6, 0x88cc7691, 0xf5024c25,
      0x4fe5d7fc, 0xc52acbd7, 0x26354480, 0xb562a38f,
      0xdeb15a49, 0x25ba1b67, 0x45ea0e98, 0x5dfec0e1,
      0xc32f7502, 0x814cf012, 0x8d4697a3, 0x6bd3f9c6,
      0x038f5fe7, 0x15929c95, 0xbf6d7aeb, 0x955259da,
      0xd4be832d, 0x587421d3, 0x49e06929, 0x8ec9c844,
      0x75c2896a, 0xf48e7978, 0x99583e6b, 0x27b971dd,
      0xbee14fb6, 0xf088ad17, 0xc920ac66, 0x7dce3ab4,
      0x63df4a18, 0xe51a3182, 0x97513360, 0x62537f45,
      0xb16477e0, 0xbb6bae84, 0xfe81a01c, 0xf9082b94,
      0x70486858, 0x8f45fd19, 0x94de6c87, 0x527bf8b7,
      0xab73d323, 0x724b02e2, 0xe31f8f57, 0x6655ab2a,
      0xb2eb2807, 0x2fb5c203, 0x86c57b9a, 0xd33708a5,
      0x302887f2, 0x23bfa5b2, 0x02036aba, 0xed16825c,
      0x8acf1c2b, 0xa779b492, 0xf307f2f0, 0x4e69e2a1,
      0x65daf4cd, 0x0605bed5, 0xd134621f, 0xc4a6fe8a,
      0x342e539d, 0xa2f355a0, 0x058ae132, 0xa4f6eb75,
      0x0b83ec39, 0x4060efaa, 0x5e719f06, 0xbd6e1051,
      0x3e218af9, 0x96dd063d, 0xdd3e05ae, 0x4de6bd46,
      0x91548db5, 0x71c45d05, 0x0406d46f, 0x605015ff,
      0x1998fb24, 0xd6bde997, 0x894043cc, 0x67d99e77,
      0xb0e842bd, 0x07898b88, 0xe7195b38, 0x79c8eedb,
      0xa17c0a47, 0x7c420fe9, 0xf8841ec9, 0x00000000,
      0x09808683, 0x322bed48, 0x1e1170ac, 0x6c5a724e,
      0xfd0efffb, 0x0f853856, 0x3daed51e, 0x362d3927,
      0x0a0fd964, 0x685ca621, 0x9b5b54d1, 0x24362e3a,
      0x0c0a67b1, 0x9357e70f, 0xb4ee96d2, 0x1b9b919e,
      0x80c0c54f, 0x61dc20a2, 0x5a774b69, 0x1c121a16,
      0xe293ba0a, 0xc0a02ae5, 0x3c22e043, 0x121b171d,
      0x0e090d0b, 0xf28bc7ad, 0x2db6a8b9, 0x141ea9c8,
      0x57f11985, 0xaf75074c, 0xee99ddbb, 0xa37f60fd,
      0xf701269f, 0x5c72f5bc, 0x44663bc5, 0x5bfb7e34,
      0x8b432976, 0xcb23c6dc, 0xb6edfc68, 0xb8e4f163,
      0xd731dcca, 0x42638510, 0x13972240, 0x84c61120,
      0x854a247d, 0xd2bb3df8, 0xaef93211, 0xc729a16d,
      0x1d9e2f4b, 0xdcb230f3, 0x0d8652ec, 0x77c1e3d0,
      0x2bb3166c, 0xa970b999, 0x119448fa, 0x47e96422,
      0xa8fc8cc4, 0xa0f03f1a, 0x567d2cd8, 0x223390ef,
      0x87494ec7, 0xd938d1c1, 0x8ccaa2fe, 0x98d40b36,
      0xa6f581cf, 0xa57ade28, 0xdab78e26, 0x3fadbfa4,
      0x2c3a9de4, 0x5078920d, 0x6a5fcc9b, 0x547e4662,
      0xf68d13c2, 0x90d8b8e8, 0x2e39f75e, 0x82c3aff5,
      0x9f5d80be, 0x69d0937c, 0x6fd52da9, 0xcf2512b3,
      0xc8ac993b, 0x10187da7, 0xe89c636e, 0xdb3bbb7b,
      0xcd267809, 0x6e5918f4, 0xec9ab701, 0x834f9aa8,
      0xe6956e65, 0xaaffe67e, 0x21bccf08, 0xef15e8e6,
      0xbae79bd9, 0x4a6f36ce, 0xea9f09d4, 0x29b07cd6,
      0x31a4b2af, 0x2a3f2331, 0xc6a59430, 0x35a266c0,
      0x744ebc37, 0xfc82caa6, 0xe090d0b0, 0x33a7d815,
      0xf104984a, 0x41ecdaf7, 0x7fcd500e, 0x1791f62f,
      0x764dd68d, 0x43efb04d, 0xccaa4d54, 0xe49604df,
      0x9ed1b5e3, 0x4c6a881b, 0xc12c1fb8, 0x4665517f,
      0x9d5eea04, 0x018c355d, 0xfa877473, 0xfb0b412e,
      0xb3671d5a, 0x92dbd252, 0xe9105633, 0x6dd64713,
      0x9ad7618c, 0x37a10c7a, 0x59f8148e, 0xeb133c89,
      0xcea927ee, 0xb761c935, 0xe11ce5ed, 0x7a47b13c,
      0x9cd2df59, 0x55f2733f, 0x1814ce79, 0x73c737bf,
      0x53f7cdea, 0x5ffdaa5b, 0xdf3d6f14, 0x7844db86,
      0xcaaff381, 0xb968c43e, 0x3824342c, 0xc2a3405f,
      0x161dc372, 0xbce2250c, 0x283c498b, 0xff0d9541,
      0x39a80171, 0x080cb3de, 0xd8b4e49c, 0x6456c190,
      0x7bcb8461, 0xd532b670, 0x486c5c74, 0xd0b85742
    };
    static const uint8_t rsb_consts[256] = {
      0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38,
      0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
      0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87,
      0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
      0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d,
      0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
      0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2,
      0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
      0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16,
      0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
      0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda,
      0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
      0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a,
      0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
      0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02,
      0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
      0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea,
      0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
      0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85,
      0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
      0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89,
      0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
      0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20,
      0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
      0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31,
      0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
      0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d,
      0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
      0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0,
      0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
      0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26,
      0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d
    };

    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "aescrypt_decryptBlock");

    // Allocate registers
    Register src = A0;
    Register dst = A1;
    Register key = A2;
    Register rve = A3;
    Register srclen = A4;
    Register keylen = T8;
    Register srcend = A5;
    Register t0 = A6;
    Register t1 = A7;
    Register t2, t3, rtp, rvp;
    Register xa[4] = { T0, T1, T2, T3 };
    Register ya[4] = { T4, T5, T6, T7 };

    Label loop, tail, done;
    address start = __ pc();

    if (cbc) {
      t2 = S0;
      t3 = S1;
      rtp = S2;
      rvp = S3;

      __ beqz(srclen, done);

      __ addi_d(SP, SP, -4 * wordSize);
      __ st_d(S3, SP, 3 * wordSize);
      __ st_d(S2, SP, 2 * wordSize);
      __ st_d(S1, SP, 1 * wordSize);
      __ st_d(S0, SP, 0 * wordSize);

      __ add_d(srcend, src, srclen);
      __ move(rvp, rve);
    } else {
      t2 = A3;
      t3 = A4;
      rtp = A5;
    }

    __ ld_w(keylen, key, arrayOopDesc::length_offset_in_bytes() - arrayOopDesc::base_offset_in_bytes(T_INT));

    __ bind(loop);

    // Round 1
    for (int i = 0; i < 4; i++) {
      __ ld_w(xa[i], src, 4 * i);
    }
    for (int i = 0; i < 4; i++) {
      __ ld_w(ya[i], key, 4 * (4 + i));
    }
    for (int i = 0; i < 4; i++) {
      __ revb_2h(xa[i], xa[i]);
    }
    for (int i = 0; i < 4; i++) {
      __ rotri_w(xa[i], xa[i], 16);
    }
    for (int i = 0; i < 4; i++) {
      __ XOR(xa[i], xa[i], ya[i]);
    }

    __ li(rtp, (intptr_t)rt_consts);

    // Round 2 - (N-1)
    for (int r = 0; r < 14; r++) {
      Register *xp;
      Register *yp;

      if (r & 1) {
        xp = xa;
        yp = ya;
      } else {
        xp = ya;
        yp = xa;
      }

      for (int i = 0; i < 4; i++) {
        __ ld_w(xp[i], key, 4 * (4 * (r + 1) + 4 + i));
      }

      for (int i = 0; i < 4; i++) {
        __ bstrpick_d(t0, yp[(i + 1) & 3], 7, 0);
        __ bstrpick_d(t1, yp[(i + 2) & 3], 15, 8);
        __ bstrpick_d(t2, yp[(i + 3) & 3], 23, 16);
        __ bstrpick_d(t3, yp[(i + 0) & 3], 31, 24);
        __ slli_w(t0, t0, 2);
        __ slli_w(t1, t1, 2);
        __ slli_w(t2, t2, 2);
        __ slli_w(t3, t3, 2);
        __ ldx_w(t0, rtp, t0);
        __ ldx_w(t1, rtp, t1);
        __ ldx_w(t2, rtp, t2);
        __ ldx_w(t3, rtp, t3);
        __ rotri_w(t0, t0, 24);
        __ rotri_w(t1, t1, 16);
        __ rotri_w(t2, t2, 8);
        __ XOR(xp[i], xp[i], t0);
        __ XOR(t0, t1, t2);
        __ XOR(xp[i], xp[i], t3);
        __ XOR(xp[i], xp[i], t0);
      }

      if (r == 8) {
        // AES 128
        __ li(t0, 44);
        __ beq(t0, keylen, tail);
      } else if (r == 10) {
        // AES 192
        __ li(t0, 52);
        __ beq(t0, keylen, tail);
      }
    }

    __ bind(tail);
    __ li(rtp, (intptr_t)rsb_consts);

    // Round N
    for (int i = 0; i < 4; i++) {
      __ bstrpick_d(t0, ya[(i + 1) & 3], 7, 0);
      __ bstrpick_d(t1, ya[(i + 2) & 3], 15, 8);
      __ bstrpick_d(t2, ya[(i + 3) & 3], 23, 16);
      __ bstrpick_d(t3, ya[(i + 0) & 3], 31, 24);
      __ ldx_bu(t0, rtp, t0);
      __ ldx_bu(t1, rtp, t1);
      __ ldx_bu(t2, rtp, t2);
      __ ldx_bu(t3, rtp, t3);
      __ ld_w(xa[i], key, 4 * i);
      __ slli_w(t1, t1, 8);
      __ slli_w(t2, t2, 16);
      __ slli_w(t3, t3, 24);
      __ XOR(xa[i], xa[i], t0);
      __ XOR(t0, t1, t2);
      __ XOR(xa[i], xa[i], t3);
      __ XOR(xa[i], xa[i], t0);
    }

    if (cbc) {
      for (int i = 0; i < 4; i++) {
        __ ld_w(ya[i], rvp, 4 * i);
      }
    }
    for (int i = 0; i < 4; i++) {
      __ revb_2h(xa[i], xa[i]);
    }
    for (int i = 0; i < 4; i++) {
      __ rotri_w(xa[i], xa[i], 16);
    }
    if (cbc) {
      for (int i = 0; i < 4; i++) {
        __ XOR(xa[i], xa[i], ya[i]);
      }
    }
    for (int i = 0; i < 4; i++) {
      __ st_w(xa[i], dst, 4 * i);
    }

    if (cbc) {
      __ move(rvp, src);
      __ addi_d(src, src, 16);
      __ addi_d(dst, dst, 16);
      __ blt(src, srcend, loop);

      __ ld_d(t0, src, -16);
      __ ld_d(t1, src, -8);
      __ st_d(t0, rve, 0);
      __ st_d(t1, rve, 8);

      __ ld_d(S3, SP, 3 * wordSize);
      __ ld_d(S2, SP, 2 * wordSize);
      __ ld_d(S1, SP, 1 * wordSize);
      __ ld_d(S0, SP, 0 * wordSize);
      __ addi_d(SP, SP, 4 * wordSize);

      __ bind(done);
      __ move(A0, srclen);
    }

    __ jr(RA);

    return start;
  }

  // Arguments:
  //
  // Inputs:
  //   A0        - byte[]  source+offset
  //   A1        - int[]   SHA.state
  //   A2        - int     offset
  //   A3        - int     limit
  //
  void generate_md5_implCompress(const char *name, address &entry, address &entry_mb) {
    static const uint32_t round_consts[64] = {
      0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
      0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
      0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
      0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
      0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
      0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
      0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
      0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
      0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
      0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
      0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
      0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
      0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
      0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
      0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
      0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
    };
    static const uint8_t round_offs[64] = {
      0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      1, 6, 11, 0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12,
      5, 8, 11, 14, 1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 15, 2,
      0, 7, 14, 5, 12, 3, 10, 1, 8, 15, 6, 13, 4, 11, 2, 9,
    };
    static const uint8_t round_shfs[64] = {
      25, 20, 15, 10, 25, 20, 15, 10, 25, 20, 15, 10, 25, 20, 15, 10,
      27, 23, 18, 12, 27, 23, 18, 12, 27, 23, 18, 12, 27, 23, 18, 12,
      28, 21, 16,  9, 28, 21, 16,  9, 28, 21, 16,  9, 28, 21, 16,  9,
      26, 22, 17, 11, 26, 22, 17, 11, 26, 22, 17, 11, 26, 22, 17, 11,
    };
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    Label loop;

    // Allocate registers
    Register t0 = T4;
    Register t1 = T5;
    Register t2 = T6;
    Register t3 = T7;
    Register buf = A0;
    Register state = A1;
    Register ofs = A2;
    Register limit = A3;
    Register kptr = T8;
    Register sa[4] = { T0, T1, T2, T3 };
    Register sb[4] = { A4, A5, A6, A7 };

    // Entry
    entry = __ pc();
    __ move(ofs, R0);
    __ move(limit, R0);

    // Entry MB
    entry_mb = __ pc();

    // Load keys base address
    __ li(kptr, (intptr_t)round_consts);

    // Load states
    __ ld_w(sa[0], state, 0);
    __ ld_w(sa[1], state, 4);
    __ ld_w(sa[2], state, 8);
    __ ld_w(sa[3], state, 12);

    __ bind(loop);
    __ move(sb[0], sa[0]);
    __ move(sb[1], sa[1]);
    __ move(sb[2], sa[2]);
    __ move(sb[3], sa[3]);

    // 64 rounds of hashing
    for (int i = 0; i < 64; i++) {
      Register a = sa[(0 - i) & 3];
      Register b = sa[(1 - i) & 3];
      Register c = sa[(2 - i) & 3];
      Register d = sa[(3 - i) & 3];

      __ ld_w(t2, kptr, i * 4);
      __ ld_w(t3, buf, round_offs[i] * 4);

      if (i < 16) {
        __ XOR(t0, c, d);
        __ AND(t0, t0, b);
        __ XOR(t0, t0, d);
      } else if (i < 32) {
        __ andn(t0, c, d);
        __ AND(t1, d, b);
        __ OR(t0, t0, t1);
      } else if (i < 48) {
        __ XOR(t0, c, d);
        __ XOR(t0, t0, b);
      } else {
        __ orn(t0, b, d);
        __ XOR(t0, t0, c);
      }

      __ add_w(a, a, t2);
      __ add_w(a, a, t3);
      __ add_w(a, a, t0);
      __ rotri_w(a, a, round_shfs[i]);
      __ add_w(a, a, b);
    }

    __ add_w(sa[0], sa[0], sb[0]);
    __ add_w(sa[1], sa[1], sb[1]);
    __ add_w(sa[2], sa[2], sb[2]);
    __ add_w(sa[3], sa[3], sb[3]);

    __ addi_w(ofs, ofs, 64);
    __ addi_d(buf, buf, 64);
    __ bge(limit, ofs, loop);
    __ move(V0, ofs); // return ofs

    // Save updated state
    __ st_w(sa[0], state, 0);
    __ st_w(sa[1], state, 4);
    __ st_w(sa[2], state, 8);
    __ st_w(sa[3], state, 12);

    __ jr(RA);
  }

  // Arguments:
  //
  // Inputs:
  //   A0        - byte[]  source+offset
  //   A1        - int[]   SHA.state
  //   A2        - int     offset
  //   A3        - int     limit
  //
  void generate_sha1_implCompress(const char *name, address &entry, address &entry_mb) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    Label keys, loop;

    // Keys
    __ bind(keys);
    __ emit_int32(0x5a827999);
    __ emit_int32(0x6ed9eba1);
    __ emit_int32(0x8f1bbcdc);
    __ emit_int32(0xca62c1d6);

    // Allocate registers
    Register t0 = T5;
    Register t1 = T6;
    Register t2 = T7;
    Register t3 = T8;
    Register buf = A0;
    Register state = A1;
    Register ofs = A2;
    Register limit = A3;
    Register ka[4] = { A4, A5, A6, A7 };
    Register sa[5] = { T0, T1, T2, T3, T4 };

    // Entry
    entry = __ pc();
    __ move(ofs, R0);
    __ move(limit, R0);

    // Entry MB
    entry_mb = __ pc();

    // Allocate scratch space
    __ addi_d(SP, SP, -64);

    // Load keys
    __ lipc(t0, keys);
    __ ld_w(ka[0], t0, 0);
    __ ld_w(ka[1], t0, 4);
    __ ld_w(ka[2], t0, 8);
    __ ld_w(ka[3], t0, 12);

    __ bind(loop);
    // Load arguments
    __ ld_w(sa[0], state, 0);
    __ ld_w(sa[1], state, 4);
    __ ld_w(sa[2], state, 8);
    __ ld_w(sa[3], state, 12);
    __ ld_w(sa[4], state, 16);

    // 80 rounds of hashing
    for (int i = 0; i < 80; i++) {
      Register a = sa[(5 - (i % 5)) % 5];
      Register b = sa[(6 - (i % 5)) % 5];
      Register c = sa[(7 - (i % 5)) % 5];
      Register d = sa[(8 - (i % 5)) % 5];
      Register e = sa[(9 - (i % 5)) % 5];

      if (i < 16) {
        __ ld_w(t0, buf, i * 4);
        __ revb_2h(t0, t0);
        __ rotri_w(t0, t0, 16);
        __ add_w(e, e, t0);
        __ st_w(t0, SP, i * 4);
        __ XOR(t0, c, d);
        __ AND(t0, t0, b);
        __ XOR(t0, t0, d);
      } else {
        __ ld_w(t0, SP, ((i - 3) & 0xF) * 4);
        __ ld_w(t1, SP, ((i - 8) & 0xF) * 4);
        __ ld_w(t2, SP, ((i - 14) & 0xF) * 4);
        __ ld_w(t3, SP, ((i - 16) & 0xF) * 4);
        __ XOR(t0, t0, t1);
        __ XOR(t0, t0, t2);
        __ XOR(t0, t0, t3);
        __ rotri_w(t0, t0, 31);
        __ add_w(e, e, t0);
        __ st_w(t0, SP, (i & 0xF) * 4);

        if (i < 20) {
          __ XOR(t0, c, d);
          __ AND(t0, t0, b);
          __ XOR(t0, t0, d);
        } else if (i < 40 || i >= 60) {
          __ XOR(t0, b, c);
          __ XOR(t0, t0, d);
        } else if (i < 60) {
          __ OR(t0, c, d);
          __ AND(t0, t0, b);
          __ AND(t2, c, d);
          __ OR(t0, t0, t2);
        }
      }

      __ rotri_w(b, b, 2);
      __ add_w(e, e, t0);
      __ add_w(e, e, ka[i / 20]);
      __ rotri_w(t0, a, 27);
      __ add_w(e, e, t0);
    }

    // Save updated state
    __ ld_w(t0, state, 0);
    __ ld_w(t1, state, 4);
    __ ld_w(t2, state, 8);
    __ ld_w(t3, state, 12);
    __ add_w(sa[0], sa[0], t0);
    __ ld_w(t0, state, 16);
    __ add_w(sa[1], sa[1], t1);
    __ add_w(sa[2], sa[2], t2);
    __ add_w(sa[3], sa[3], t3);
    __ add_w(sa[4], sa[4], t0);
    __ st_w(sa[0], state, 0);
    __ st_w(sa[1], state, 4);
    __ st_w(sa[2], state, 8);
    __ st_w(sa[3], state, 12);
    __ st_w(sa[4], state, 16);

    __ addi_w(ofs, ofs, 64);
    __ addi_d(buf, buf, 64);
    __ bge(limit, ofs, loop);
    __ move(V0, ofs); // return ofs

    __ addi_d(SP, SP, 64);
    __ jr(RA);
  }

  // Arguments:
  //
  // Inputs:
  //   A0        - byte[]  source+offset
  //   A1        - int[]   SHA.state
  //   A2        - int     offset
  //   A3        - int     limit
  //
  void generate_sha256_implCompress(const char *name, address &entry, address &entry_mb) {
    static const uint32_t round_consts[64] = {
      0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
      0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
      0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
      0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
      0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
      0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
      0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
      0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
      0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
      0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
      0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
      0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
      0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
      0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
      0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
      0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    };
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", name);
    Label loop;

    // Allocate registers
    Register t0 = A4;
    Register t1 = A5;
    Register t2 = A6;
    Register t3 = A7;
    Register buf = A0;
    Register state = A1;
    Register ofs = A2;
    Register limit = A3;
    Register kptr = T8;
    Register sa[8] = { T0, T1, T2, T3, T4, T5, T6, T7 };

    // Entry
    entry = __ pc();
    __ move(ofs, R0);
    __ move(limit, R0);

    // Entry MB
    entry_mb = __ pc();

    // Allocate scratch space
    __ addi_d(SP, SP, -64);

    // Load keys base address
    __ li(kptr, (intptr_t)round_consts);

    __ bind(loop);
    // Load state
    __ ld_w(sa[0], state, 0);
    __ ld_w(sa[1], state, 4);
    __ ld_w(sa[2], state, 8);
    __ ld_w(sa[3], state, 12);
    __ ld_w(sa[4], state, 16);
    __ ld_w(sa[5], state, 20);
    __ ld_w(sa[6], state, 24);
    __ ld_w(sa[7], state, 28);

    // Do 64 rounds of hashing
    for (int i = 0; i < 64; i++) {
      Register a = sa[(0 - i) & 7];
      Register b = sa[(1 - i) & 7];
      Register c = sa[(2 - i) & 7];
      Register d = sa[(3 - i) & 7];
      Register e = sa[(4 - i) & 7];
      Register f = sa[(5 - i) & 7];
      Register g = sa[(6 - i) & 7];
      Register h = sa[(7 - i) & 7];

      if (i < 16) {
        __ ld_w(t1, buf, i * 4);
        __ revb_2h(t1, t1);
        __ rotri_w(t1, t1, 16);
      } else {
        __ ld_w(t0, SP, ((i - 15) & 0xF) * 4);
        __ ld_w(t1, SP, ((i - 16) & 0xF) * 4);
        __ ld_w(t2, SP, ((i - 7) & 0xF) * 4);
        __ add_w(t1, t1, t2);
        __ rotri_w(t2, t0, 18);
        __ srli_w(t3, t0, 3);
        __ rotri_w(t0, t0, 7);
        __ XOR(t2, t2, t3);
        __ XOR(t0, t0, t2);
        __ add_w(t1, t1, t0);
        __ ld_w(t0, SP, ((i - 2) & 0xF) * 4);
        __ rotri_w(t2, t0, 19);
        __ srli_w(t3, t0, 10);
        __ rotri_w(t0, t0, 17);
        __ XOR(t2, t2, t3);
        __ XOR(t0, t0, t2);
        __ add_w(t1, t1, t0);
      }

      __ rotri_w(t2, e, 11);
      __ rotri_w(t3, e, 25);
      __ rotri_w(t0, e, 6);
      __ XOR(t2, t2, t3);
      __ XOR(t0, t0, t2);
      __ XOR(t2, g, f);
      __ ld_w(t3, kptr, i * 4);
      __ AND(t2, t2, e);
      __ XOR(t2, t2, g);
      __ add_w(t0, t0, t2);
      __ add_w(t0, t0, t3);
      __ add_w(h, h, t1);
      __ add_w(h, h, t0);
      __ add_w(d, d, h);
      __ rotri_w(t2, a, 13);
      __ rotri_w(t3, a, 22);
      __ rotri_w(t0, a, 2);
      __ XOR(t2, t2, t3);
      __ XOR(t0, t0, t2);
      __ add_w(h, h, t0);
      __ OR(t0, c, b);
      __ AND(t2, c, b);
      __ AND(t0, t0, a);
      __ OR(t0, t0, t2);
      __ add_w(h, h, t0);
      __ st_w(t1, SP, (i & 0xF) * 4);
    }

    // Add to state
    __ ld_w(t0, state, 0);
    __ ld_w(t1, state, 4);
    __ ld_w(t2, state, 8);
    __ ld_w(t3, state, 12);
    __ add_w(sa[0], sa[0], t0);
    __ add_w(sa[1], sa[1], t1);
    __ add_w(sa[2], sa[2], t2);
    __ add_w(sa[3], sa[3], t3);
    __ ld_w(t0, state, 16);
    __ ld_w(t1, state, 20);
    __ ld_w(t2, state, 24);
    __ ld_w(t3, state, 28);
    __ add_w(sa[4], sa[4], t0);
    __ add_w(sa[5], sa[5], t1);
    __ add_w(sa[6], sa[6], t2);
    __ add_w(sa[7], sa[7], t3);
    __ st_w(sa[0], state, 0);
    __ st_w(sa[1], state, 4);
    __ st_w(sa[2], state, 8);
    __ st_w(sa[3], state, 12);
    __ st_w(sa[4], state, 16);
    __ st_w(sa[5], state, 20);
    __ st_w(sa[6], state, 24);
    __ st_w(sa[7], state, 28);

    __ addi_w(ofs, ofs, 64);
    __ addi_d(buf, buf, 64);
    __ bge(limit, ofs, loop);
    __ move(V0, ofs); // return ofs

    __ addi_d(SP, SP, 64);
    __ jr(RA);
  }

  // Do NOT delete this node which stands for stub routine placeholder
  address generate_updateBytesCRC32() {
    assert(UseCRC32Intrinsics, "need CRC32 instructions support");

    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "updateBytesCRC32");

    address start = __ pc();

    const Register crc = A0;  // crc
    const Register buf = A1;  // source java byte array address
    const Register len = A2;  // length
    const Register tmp = A3;

    __ enter(); // required for proper stackwalking of RuntimeStub frame

    __ kernel_crc32(crc, buf, len, tmp);

    __ leave(); // required for proper stackwalking of RuntimeStub frame
    __ jr(RA);

    return start;
  }

  // Do NOT delete this node which stands for stub routine placeholder
  address generate_updateBytesCRC32C() {
    assert(UseCRC32CIntrinsics, "need CRC32C instructions support");

    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "updateBytesCRC32C");

    address start = __ pc();

    const Register crc = A0;  // crc
    const Register buf = A1;  // source java byte array address
    const Register len = A2;  // length
    const Register tmp = A3;

    __ enter(); // required for proper stackwalking of RuntimeStub frame

    __ kernel_crc32c(crc, buf, len, tmp);

    __ leave(); // required for proper stackwalking of RuntimeStub frame
    __ jr(RA);

    return start;
  }

  // ChaCha20 block function.  This version parallelizes by loading
  // individual 32-bit state elements into vectors for four blocks
  //
  // state (int[16]) = c_rarg0
  // keystream (byte[1024]) = c_rarg1
  // return - number of bytes of keystream (always 256)
  address generate_chacha20Block_blockpar() {
    Label L_twoRounds, L_cc20_const;
    // Add masks for 4-block ChaCha20 Block calculations,
    // creates a +0/+1/+2/+3 add overlay.
    __ bind(L_cc20_const);
    __ emit_int64(0x0000000000000001UL);
    __ emit_int64(0x0000000000000000UL);

    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "chacha20Block");
    address start = __ pc();
    __ enter();

    int i;
    const Register state = c_rarg0;
    const Register keystream = c_rarg1;
    const Register loopCtr = SCR1;
    const Register tmpAddr = SCR2;

    const FloatRegister aState = F0;
    const FloatRegister bState = F1;
    const FloatRegister cState = F2;
    const FloatRegister dState = F3;
    const FloatRegister origCtrState = F20;
    const FloatRegister dState1 = F21;
    const FloatRegister dState2 = F22;
    const FloatRegister dState3 = F23;

    // Organize SIMD registers in four arrays that facilitates
    // putting repetitive opcodes into loop structures.
    const FloatRegister aVec[4] = {
      F4, F5, F6, F7
    };
    const FloatRegister bVec[4] = {
      F8, F9, F10, F11
    };
    const FloatRegister cVec[4] = {
      F12, F13, F14, F15
    };
    const FloatRegister dVec[4] = {
      F16, F17, F18, F19
    };

    // Load the initial state in columnar orientation and then copy
    // that starting state to the working register set.
    // Also load the address of the add mask for later use in handling
    // multi-block counter increments.
    __ vld(aState, state,  0);
    __ vld(bState, state, 16);
    __ vld(cState, state, 32);
    __ vld(dState, state, 48);
    __ lipc(tmpAddr, L_cc20_const);
    __ vld(origCtrState, tmpAddr, 0);
    __ vadd_w(dState1, dState, origCtrState);
    __ vadd_w(dState2, dState1, origCtrState);
    __ vadd_w(dState3, dState2, origCtrState);
    for (i = 0; i < 4; i++) {
      __ vori_b(aVec[i], aState, 0);
      __ vori_b(bVec[i], bState, 0);
      __ vori_b(cVec[i], cState, 0);
    }
    __ vori_b(dVec[0], dState, 0);
    __ vori_b(dVec[1], dState1, 0);
    __ vori_b(dVec[2], dState2, 0);
    __ vori_b(dVec[3], dState3, 0);

    // Set up the 10 iteration loop and perform all 8 quarter round ops
    __ li(loopCtr, 10);
    __ bind(L_twoRounds);

    // The first quarter round macro call covers the first 4 QR operations:
    //  Qround(state, 0, 4, 8,12)
    //  Qround(state, 1, 5, 9,13)
    //  Qround(state, 2, 6,10,14)
    //  Qround(state, 3, 7,11,15)
    __ cc20_quarter_round(aVec[0], bVec[0], cVec[0], dVec[0]);
    __ cc20_quarter_round(aVec[1], bVec[1], cVec[1], dVec[1]);
    __ cc20_quarter_round(aVec[2], bVec[2], cVec[2], dVec[2]);
    __ cc20_quarter_round(aVec[3], bVec[3], cVec[3], dVec[3]);

    // Shuffle the bVec/cVec/dVec to reorganize the state vectors
    // to diagonals. The aVec does not need to change orientation.
    __ cc20_shift_lane_org(bVec[0], cVec[0], dVec[0], true);
    __ cc20_shift_lane_org(bVec[1], cVec[1], dVec[1], true);
    __ cc20_shift_lane_org(bVec[2], cVec[2], dVec[2], true);
    __ cc20_shift_lane_org(bVec[3], cVec[3], dVec[3], true);

    // The second set of operations on the vectors covers the second 4 quarter
    // round operations, now acting on the diagonals:
    //  Qround(state, 0, 5,10,15)
    //  Qround(state, 1, 6,11,12)
    //  Qround(state, 2, 7, 8,13)
    //  Qround(state, 3, 4, 9,14)
    __ cc20_quarter_round(aVec[0], bVec[0], cVec[0], dVec[0]);
    __ cc20_quarter_round(aVec[1], bVec[1], cVec[1], dVec[1]);
    __ cc20_quarter_round(aVec[2], bVec[2], cVec[2], dVec[2]);
    __ cc20_quarter_round(aVec[3], bVec[3], cVec[3], dVec[3]);

    // Before we start the next iteration, we need to perform shuffles
    // on the b/c/d vectors to move them back to columnar organizations
    // from their current diagonal orientation.
    __ cc20_shift_lane_org(bVec[0], cVec[0], dVec[0], false);
    __ cc20_shift_lane_org(bVec[1], cVec[1], dVec[1], false);
    __ cc20_shift_lane_org(bVec[2], cVec[2], dVec[2], false);
    __ cc20_shift_lane_org(bVec[3], cVec[3], dVec[3], false);

    // Decrement and iterate
    __ addi_d(loopCtr, loopCtr, -1);
    __ bnez(loopCtr, L_twoRounds);

    // Add the original start state back into the current state.
    for (i = 0; i < 4; i++) {
      __ vadd_w(aVec[i], aVec[i], aState);
      __ vadd_w(bVec[i], bVec[i], bState);
      __ vadd_w(cVec[i], cVec[i], cState);
    }
    __ vadd_w(dVec[0], dVec[0], dState);
    __ vadd_w(dVec[1], dVec[1], dState1);
    __ vadd_w(dVec[2], dVec[2], dState2);
    __ vadd_w(dVec[3], dVec[3], dState3);

    // Write the data to the keystream array
    for (i = 0; i < 4; i++) {
        __ vst(aVec[i], keystream, 0);
        __ vst(bVec[i], keystream, 16);
        __ vst(cVec[i], keystream, 32);
        __ vst(dVec[i], keystream, 48);
        __ addi_d(keystream, keystream, 64);
    }

    __ li(A0, 256);             // Return length of output keystream
    __ leave();
    __ jr(RA);

    return start;
  }

  // Arguments:
  //
  // Input:
  //   c_rarg0   - newArr address
  //   c_rarg1   - oldArr address
  //   c_rarg2   - newIdx
  //   c_rarg3   - shiftCount
  //   c_rarg4   - numIter
  //
  address generate_bigIntegerLeftShift() {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "bigIntegerLeftShiftWorker");
    address entry = __ pc();

    Label loop_eight, loop_four, once, exit;

    Register newArr        = c_rarg0;
    Register oldArr        = c_rarg1;
    Register newIdx        = c_rarg2;
    Register shiftCount    = c_rarg3;
    Register numIter       = c_rarg4;

    Register shiftRevCount = c_rarg5;

    FloatRegister vShiftCount    = c_farg0;
    FloatRegister vShiftRevCount = c_farg1;

    __ beqz(numIter, exit);

    __ alsl_d(newArr, newIdx, newArr, 1);
    __ li(shiftRevCount, 32);
    __ sub_w(shiftRevCount, shiftRevCount, shiftCount);

    __ li(SCR2, 4);
    __ blt(numIter, SCR2, once);

    __ xvreplgr2vr_w(vShiftCount, shiftCount);
    __ xvreplgr2vr_w(vShiftRevCount, shiftRevCount);

    __ li(SCR1, 8);
    __ blt(numIter, SCR1, loop_four);

    __ bind(loop_eight);
    __ xvld(FT0, oldArr, 0);
    __ xvld(FT1, oldArr, 4);
    __ xvsll_w(FT0, FT0, vShiftCount);
    __ xvsrl_w(FT1, FT1, vShiftRevCount);
    __ xvor_v(FT0, FT0, FT1);
    __ xvst(FT0, newArr, 0);
    __ addi_d(numIter, numIter, -8);
    __ addi_d(oldArr, oldArr, 32);
    __ addi_d(newArr, newArr, 32);
    __ bge(numIter, SCR1, loop_eight);

    __ bind(loop_four);
    __ blt(numIter, SCR2, once);
    __ vld(FT0, oldArr, 0);
    __ vld(FT1, oldArr, 4);
    __ vsll_w(FT0, FT0, vShiftCount);
    __ vsrl_w(FT1, FT1, vShiftRevCount);
    __ vor_v(FT0, FT0, FT1);
    __ vst(FT0, newArr, 0);
    __ addi_d(numIter, numIter, -4);
    __ addi_d(oldArr, oldArr, 16);
    __ addi_d(newArr, newArr, 16);
    __ b(loop_four);

    __ bind(once);
    __ beqz(numIter, exit);
    __ ld_w(SCR1, oldArr, 0);
    __ ld_w(SCR2, oldArr, 4);
    __ sll_w(SCR1, SCR1, shiftCount);
    __ srl_w(SCR2, SCR2, shiftRevCount);
    __ orr(SCR1, SCR1, SCR2);
    __ st_w(SCR1, newArr, 0);
    __ addi_d(numIter, numIter, -1);
    __ addi_d(oldArr, oldArr, 4);
    __ addi_d(newArr, newArr, 4);
    __ b(once);

    __ bind(exit);
    __ jr(RA);

    return entry;
  }

  address generate_bigIntegerRightShift() {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "bigIntegerRightShiftWorker");
    address entry = __ pc();

    Label loop_eight, loop_four, once, exit;

    Register newArr        = c_rarg0;
    Register oldArr        = c_rarg1;
    Register newIdx        = c_rarg2;
    Register shiftCount    = c_rarg3;
    Register numIter       = c_rarg4;
    Register nidx          = numIter;

    Register shiftRevCount = c_rarg5;

    FloatRegister vShiftCount    = c_farg0;
    FloatRegister vShiftRevCount = c_farg1;

    __ beqz(nidx, exit);

    __ alsl_d(newArr, newIdx, newArr, 1);
    __ alsl_d(newArr, nidx, newArr, 1);
    __ alsl_d(oldArr, numIter, oldArr, 1);

    __ li(shiftRevCount, 32);
    __ sub_w(shiftRevCount, shiftRevCount, shiftCount);

    __ li(SCR2, 4);
    __ blt(nidx, SCR2, once);

    __ xvreplgr2vr_w(vShiftCount, shiftCount);
    __ xvreplgr2vr_w(vShiftRevCount, shiftRevCount);

    __ li(SCR1, 8);
    __ blt(nidx, SCR1, loop_four);

    __ bind(loop_eight);

    __ addi_d(nidx, nidx, -8);
    __ addi_d(oldArr, oldArr, -32);
    __ addi_d(newArr, newArr, -32);

    __ xvld(FT0, oldArr, 4);
    __ xvld(FT1, oldArr, 0);
    __ xvsrl_w(FT0, FT0, vShiftCount);
    __ xvsll_w(FT1, FT1, vShiftRevCount);
    __ xvor_v(FT0, FT0, FT1);
    __ xvst(FT0, newArr, 0);
    __ bge(nidx, SCR1, loop_eight);

    __ bind(loop_four);
    __ blt(nidx, SCR2, once);
    __ addi_d(nidx, nidx, -4);
    __ addi_d(oldArr, oldArr, -16);
    __ addi_d(newArr, newArr, -16);
    __ xvld(FT0, oldArr, 4);
    __ xvld(FT1, oldArr, 0);
    __ xvsrl_w(FT0, FT0, vShiftCount);
    __ xvsll_w(FT1, FT1, vShiftRevCount);
    __ vor_v(FT0, FT0, FT1);
    __ vst(FT0, newArr, 0);

    __ b(loop_four);

    __ bind(once);
    __ beqz(nidx, exit);
    __ addi_d(nidx, nidx, -1);
    __ addi_d(oldArr, oldArr, -4);
    __ addi_d(newArr, newArr, -4);
    __ ld_w(SCR1, oldArr, 4);
    __ ld_w(SCR2, oldArr, 0);
    __ srl_w(SCR1, SCR1, shiftCount);
    __ sll_w(SCR2, SCR2, shiftRevCount);
    __ orr(SCR1, SCR1, SCR2);
    __ st_w(SCR1, newArr, 0);

    __ b(once);

    __ bind(exit);
    __ jr(RA);

    return entry;
  }

  address generate_dsin_dcos(bool isCos) {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", isCos ? "libmDcos" : "libmDsin");
    address start = __ pc();
    __ generate_dsin_dcos(isCos, (address)StubRoutines::la::_npio2_hw,
                                 (address)StubRoutines::la::_two_over_pi,
                                 (address)StubRoutines::la::_pio2,
                                 (address)StubRoutines::la::_dsin_coef,
                                 (address)StubRoutines::la::_dcos_coef);
    return start;
  }

  address generate_cont_thaw(Continuation::thaw_kind kind) {
    bool return_barrier = Continuation::is_thaw_return_barrier(kind);
    bool return_barrier_exception = Continuation::is_thaw_return_barrier_exception(kind);

    address start = __ pc();

    if (return_barrier) {
      __ ld_d(SP, Address(TREG, JavaThread::cont_entry_offset()));
    }

#ifndef PRODUCT
    {
      Label OK;
      __ ld_d(AT, Address(TREG, JavaThread::cont_entry_offset()));
      __ beq(SP, AT, OK);
      __ stop("incorrect sp before prepare_thaw");
      __ bind(OK);
    }
#endif

    if (return_barrier) {
      // preserve possible return value from a method returning to the return barrier
      __ addi_d(SP, SP, - 2 * wordSize);
      __ fst_d(FA0, Address(SP, 0 * wordSize));
      __ st_d(A0, Address(SP, 1 * wordSize));
    }

    __ addi_w(c_rarg1, R0, (return_barrier ? 1 : 0));
    __ call_VM_leaf(CAST_FROM_FN_PTR(address, Continuation::prepare_thaw), TREG, c_rarg1);
    __ move(T4, A0); // A0 contains the size of the frames to thaw, 0 if overflow or no more frames

    if (return_barrier) {
      // restore return value (no safepoint in the call to thaw, so even an oop return value should be OK)
      __ ld_d(A0, Address(SP, 1 * wordSize));
      __ fld_d(FA0, Address(SP, 0 * wordSize));
      __ addi_d(SP, SP, 2 * wordSize);
    }

#ifndef PRODUCT
    {
      Label OK;
      __ ld_d(AT, Address(TREG, JavaThread::cont_entry_offset()));
      __ beq(SP, AT, OK);
      __ stop("incorrect sp after prepare_thaw");
      __ bind(OK);
    }
#endif

    Label thaw_success;
    // T4 contains the size of the frames to thaw, 0 if overflow or no more frames
    __ bnez(T4, thaw_success);
    __ jmp(SharedRuntime::throw_StackOverflowError_entry());
    __ bind(thaw_success);

    // make room for the thawed frames
    __ sub_d(SP, SP, T4);
    assert(StackAlignmentInBytes == 16, "must be");
    __ bstrins_d(SP, R0, 3, 0);

    if (return_barrier) {
      // save original return value -- again
      __ addi_d(SP, SP, - 2 * wordSize);
      __ fst_d(FA0, Address(SP, 0 * wordSize));
      __ st_d(A0, Address(SP, 1 * wordSize));
    }

    // If we want, we can templatize thaw by kind, and have three different entries
    __ li(c_rarg1, (uint32_t)kind);

    __ call_VM_leaf(Continuation::thaw_entry(), TREG, c_rarg1);
    __ move(T4, A0); // A0 is the sp of the yielding frame

    if (return_barrier) {
      // restore return value (no safepoint in the call to thaw, so even an oop return value should be OK)
      __ ld_d(A0, Address(SP, 1 * wordSize));
      __ fld_d(FA0, Address(SP, 0 * wordSize));
      __ addi_d(SP, SP, 2 * wordSize);
    } else {
      __ move(A0, R0); // return 0 (success) from doYield
    }

    // we're now on the yield frame (which is in an address above us b/c sp has been pushed down)
    __ move(FP, T4);
    __ addi_d(SP, T4, - 2 * wordSize); // now pointing to fp spill

    if (return_barrier_exception) {
      __ ld_d(c_rarg1, Address(FP, -1 * wordSize)); // return address
      __ verify_oop(A0);
      __ move(TSR, A0); // save return value contaning the exception oop in callee-saved TSR

      __ call_VM_leaf(CAST_FROM_FN_PTR(address, SharedRuntime::exception_handler_for_return_address), TREG, c_rarg1);

      // Continue at exception handler:
      //   A0: exception oop
      //   T4: exception handler
      //   A1: exception pc
      __ move(T4, A0);
      __ move(A0, TSR);
      __ verify_oop(A0);

      __ leave();
      __ move(A1, RA);
      __ jr(T4);
    } else {
      // We're "returning" into the topmost thawed frame; see Thaw::push_return_frame
      __ leave();
      __ jr(RA);
    }

    return start;
  }

  address generate_cont_thaw() {
    if (!Continuations::enabled()) return nullptr;

    StubCodeMark mark(this, "StubRoutines", "Cont thaw");
    address start = __ pc();
    generate_cont_thaw(Continuation::thaw_top);
    return start;
  }

  address generate_cont_returnBarrier() {
    if (!Continuations::enabled()) return nullptr;

    // TODO: will probably need multiple return barriers depending on return type
    StubCodeMark mark(this, "StubRoutines", "cont return barrier");
    address start = __ pc();

    generate_cont_thaw(Continuation::thaw_return_barrier);

    return start;
  }

  address generate_cont_returnBarrier_exception() {
    if (!Continuations::enabled()) return nullptr;

    StubCodeMark mark(this, "StubRoutines", "cont return barrier exception handler");
    address start = __ pc();

    generate_cont_thaw(Continuation::thaw_return_barrier_exception);

    return start;
  }

  address generate_cont_preempt_stub() {
    if (!Continuations::enabled()) return nullptr;
    StubCodeMark mark(this, "StubRoutines","Continuation preempt stub");
    address start = __ pc();

    __ reset_last_Java_frame(true);

    // Set sp to enterSpecial frame, i.e. remove all frames copied into the heap.
    __ ld_d(SP, Address(TREG, JavaThread::cont_entry_offset()));

    Label preemption_cancelled;
    __ ld_bu(AT, Address(TREG, JavaThread::preemption_cancelled_offset()));
    __ bnez(AT, preemption_cancelled);

    // Remove enterSpecial frame from the stack and return to Continuation.run() to unmount.
    SharedRuntime::continuation_enter_cleanup(_masm);
    __ leave();
    __ jr(RA);

    // We acquired the monitor after freezing the frames so call thaw to continue execution.
    __ bind(preemption_cancelled);
    __ st_b(R0, Address(TREG, JavaThread::preemption_cancelled_offset()));
    __ addi_d(FP, SP, checked_cast<int32_t>(ContinuationEntry::size() + 2 * wordSize));
    __ li(AT, ContinuationEntry::thaw_call_pc_address());
    __ ld_d(AT, AT, 0);
    __ jr(AT);

    return start;
  }

#ifdef COMPILER2

static const int64_t right_2_bits = right_n_bits(2);
static const int64_t right_3_bits = right_n_bits(3);

  // In sun.security.util.math.intpoly.IntegerPolynomial1305, integers
  // are represented as long[5], with BITS_PER_LIMB = 26.
  // Pack five 26-bit limbs into three 64-bit registers.
  void poly1305_pack_26(Register dest0, Register dest1, Register dest2, Register src, Register tmp1, Register tmp2) {
    assert_different_registers(dest0, dest1, dest2, src, tmp1, tmp2);

    // The goal is to have 128-bit value in dest2:dest1:dest0
    __ ld_d(dest0, Address(src, 0));    // 26 bits in dest0

    __ ld_d(tmp1, Address(src, sizeof(jlong)));
    __ slli_d(tmp1, tmp1, 26);
    __ add_d(dest0, dest0, tmp1);       // 52 bits in dest0

    __ ld_d(tmp2, Address(src, 2 * sizeof(jlong)));
    __ slli_d(tmp1, tmp2, 52);
    __ add_d(dest0, dest0, tmp1);       // dest0 is full

    __ srli_d(dest1, tmp2, 12);         // 14-bit in dest1

    __ ld_d(tmp1, Address(src, 3 * sizeof(jlong)));
    __ slli_d(tmp1, tmp1, 14);
    __ add_d(dest1, dest1, tmp1);       // 40-bit in dest1

    __ ld_d(tmp1, Address(src, 4 * sizeof(jlong)));
    __ slli_d(tmp2, tmp1, 40);
    __ add_d(dest1, dest1, tmp2);       // dest1 is full

    if (dest2->is_valid()) {
      __ srli_d(tmp1, tmp1, 24);
      __ move(dest2, tmp1);               // 2 bits in dest2
    } else {
#ifdef ASSERT
      Label OK;
      __ srli_d(tmp1, tmp1, 24);
      __ beq(R0, tmp1, OK);           // 2 bits
      __ stop("high bits of Poly1305 integer should be zero");
      __ should_not_reach_here();
      __ bind(OK);
#endif
    }
  }

  // As above, but return only a 128-bit integer, packed into two
  // 64-bit registers.
  void poly1305_pack_26(Register dest0, Register dest1, Register src, Register tmp1, Register tmp2) {
    poly1305_pack_26(dest0, dest1, noreg, src, tmp1, tmp2);
  }

  // U_2:U_1:U_0: += (U_2 >> 2) * 5
  void poly1305_reduce(Register U_2, Register U_1, Register U_0, Register tmp1, Register tmp2) {
    assert_different_registers(U_2, U_1, U_0, tmp1, tmp2);

    // First, U_2:U_1:U_0 += (U_2 >> 2)
    __ srli_d(tmp1, U_2, 2);
    __ cad(U_0, U_0, tmp1, tmp2); // Add tmp1 to U_0 with carry output to tmp2
    __ andi(U_2, U_2, right_2_bits); // Clear U_2 except for the lowest two bits
    __ cad(U_1, U_1, tmp2, tmp2); // Add carry to U_1 with carry output to tmp2
    __ add_d(U_2, U_2, tmp2);

    // Second, U_2:U_1:U_0 += (U_2 >> 2) << 2
    __ slli_d(tmp1, tmp1, 2);
    __ cad(U_0, U_0, tmp1, tmp2); // Add tmp1 to U_0 with carry output to tmp2
    __ cad(U_1, U_1, tmp2, tmp2); // Add carry to U_1 with carry output to tmp2
    __ add_d(U_2, U_2, tmp2);
  }

  // Poly1305, RFC 7539
  // void com.sun.crypto.provider.Poly1305.processMultipleBlocks(byte[] input, int offset, int length, long[] aLimbs, long[] rLimbs)

  // Arguments:
  //    c_rarg0:   input_start -- where the input is stored
  //    c_rarg1:   length
  //    c_rarg2:   acc_start -- where the output will be stored
  //    c_rarg3:   r_start -- where the randomly generated 128-bit key is stored

  // See https://loup-vaillant.fr/tutorials/poly1305-design for a
  // description of the tricks used to simplify and accelerate this
  // computation.

  address generate_poly1305_processBlocks() {
    __ align(CodeEntryAlignment);
    StubCodeMark mark(this, "StubRoutines", "poly1305_processBlocks");
    address start = __ pc();
    __ enter();
    Label here;

    RegSet saved_regs = RegSet::of(S0);
    RegSetIterator<Register> regs = (RegSet::range(A4, T8) - RegSet::of(SCR1, SCR2) + RegSet::of(S0)).begin();
    __ push(saved_regs);

    // Arguments
    const Register input_start = c_rarg0, length = c_rarg1, acc_start = c_rarg2, r_start = c_rarg3;

    // R_n is the 128-bit randomly-generated key, packed into two
    // registers. The caller passes this key to us as long[5], with
    // BITS_PER_LIMB = 26.
    const Register R_0 = *regs, R_1 = *++regs;
    poly1305_pack_26(R_0, R_1, r_start, SCR1, SCR2);

    // RR_n is (R_n >> 2) * 5
    const Register RR_0 = *++regs, RR_1 = *++regs;
    __ srli_d(SCR1, R_0, 2);
    __ alsl_d(RR_0, SCR1, SCR1, 1);
    __ srli_d(SCR1, R_1, 2);
    __ alsl_d(RR_1, SCR1, SCR1, 1);

    // U_n is the current checksum
    const Register U_0 = *++regs, U_1 = *++regs, U_2 = *++regs;
    poly1305_pack_26(U_0, U_1, U_2, acc_start, SCR1, SCR2);

    static constexpr int BLOCK_LENGTH = 16;
    Label DONE, LOOP;

    __ li(SCR1, BLOCK_LENGTH);
    __ blt(length, SCR1, DONE);

    {
      __ bind(LOOP);

      // S_n is to be the sum of U_n and the next block of data
      const Register S_0 = *++regs, S_1 = *++regs, S_2 = *++regs;
      __ ld_d(S_0, Address(input_start, 0));
      __ ld_d(S_1, Address(input_start, wordSize));

      __ cad(S_0, S_0, U_0, SCR1); // Add U_0 to S_0 with carry output to SCR1
      __ cadc(S_1, S_1, U_1, SCR1); // Add U_1 with carry to S_1 with carry output to SCR1
      __ add_d(S_2, U_2, SCR1);

      __ addi_d(S_2, S_2, 1);

      const Register U_0HI = *++regs, U_1HI = *++regs;

      // NB: this logic depends on some of the special properties of
      // Poly1305 keys. In particular, because we know that the top
      // four bits of R_0 and R_1 are zero, we can add together
      // partial products without any risk of needing to propagate a
      // carry out.
      __ wide_mul(U_0, U_0HI, S_0, R_0);
      __ wide_madd(U_0, U_0HI, S_1, RR_1, SCR1, SCR2);
      __ wide_madd(U_0, U_0HI, S_2, RR_0, SCR1, SCR2);

      __ wide_mul(U_1, U_1HI, S_0, R_1);
      __ wide_madd(U_1, U_1HI, S_1, R_0, SCR1, SCR2);
      __ wide_madd(U_1, U_1HI, S_2, RR_1, SCR1, SCR2);

      __ andi(U_2, R_0, right_2_bits);
      __ mul_d(U_2, S_2, U_2);

      // Partial reduction mod 2**130 - 5
      __ cad(U_1, U_1, U_0HI, SCR1); // Add U_0HI to U_1 with carry output to SCR1
      __ adc(U_2, U_2, U_1HI, SCR1);
      // Sum is now in U_2:U_1:U_0.

      // U_2:U_1:U_0: += (U_2 >> 2) * 5
      poly1305_reduce(U_2, U_1, U_0, SCR1, SCR2);

      __ addi_d(length, length, -BLOCK_LENGTH);
      __ addi_d(input_start, input_start, BLOCK_LENGTH);
      __ li(SCR1, BLOCK_LENGTH);
      __ bge(length, SCR1, LOOP);
    }

    // Further reduce modulo 2^130 - 5
    poly1305_reduce(U_2, U_1, U_0, SCR1, SCR2);

    // Unpack the sum into five 26-bit limbs and write to memory.
    // First 26 bits is the first limb
    __ slli_d(SCR1, U_0, 38); // Take lowest 26 bits
    __ srli_d(SCR1, SCR1, 38);
    __ st_d(SCR1, Address(acc_start)); // First 26-bit limb

    // 27-52 bits of U_0 is the second limb
    __ slli_d(SCR1, U_0, 12); // Take next 27-52 bits
    __ srli_d(SCR1, SCR1, 38);
    __ st_d(SCR1, Address(acc_start, sizeof (jlong))); // Second 26-bit limb

    // Getting 53-64 bits of U_0 and 1-14 bits of U_1 in one register
    __ srli_d(SCR1, U_0, 52);
    __ slli_d(SCR2, U_1, 50);
    __ srli_d(SCR2, SCR2, 38);
    __ add_d(SCR1, SCR1, SCR2);
    __ st_d(SCR1, Address(acc_start, 2 * sizeof (jlong))); // Third 26-bit limb

    // Storing 15-40 bits of U_1
    __ slli_d(SCR1, U_1, 24); // Already used up 14 bits
    __ srli_d(SCR1, SCR1, 38); // Clear all other bits from SCR1
    __ st_d(SCR1, Address(acc_start, 3 * sizeof (jlong))); // Fourth 26-bit limb

    // Storing 41-64 bits of U_1 and first three bits from U_2 in one register
    __ srli_d(SCR1, U_1, 40);
    __ andi(SCR2, U_2, right_3_bits);
    __ slli_d(SCR2, SCR2, 24);
    __ add_d(SCR1, SCR1, SCR2);
    __ st_d(SCR1, Address(acc_start, 4 * sizeof (jlong))); // Fifth 26-bit limb

    __ bind(DONE);
    __ pop(saved_regs);
    __ leave(); // Required for proper stackwalking
    __ jr(RA);

    return start;
  }

  address generate_lookup_secondary_supers_table_stub(u1 super_klass_index) {
    StubCodeMark mark(this, "StubRoutines", "lookup_secondary_supers_table");

    address start = __ pc();
    const Register
      r_super_klass  = A0,
      r_array_base   = A1,
      r_array_length = A2,
      r_array_index  = A3,
      r_sub_klass    = A4,
      result         = A5,
      r_bitmap       = A6;

    Label L_success;
    __ enter();
    __ lookup_secondary_supers_table(r_sub_klass, r_super_klass, result,
                                     r_array_base, r_array_length, r_array_index,
                                     r_bitmap, super_klass_index, /*stub_is_near*/true);
    __ leave();
    __ jr(RA);

    return start;
  }

  // Slow path implementation for UseSecondarySupersTable.
  address generate_lookup_secondary_supers_table_slow_path_stub() {
    StubCodeMark mark(this, "StubRoutines", "lookup_secondary_supers_table_slow_path");

    address start = __ pc();
    const Register
      r_super_klass  = A0,        // argument
      r_array_base   = A1,        // argument
      temp1          = A2,        // tmp
      r_array_index  = A3,        // argument
      result         = A5,        // argument
      r_bitmap       = A6;        // argument

    __ lookup_secondary_supers_table_slow_path(r_super_klass, r_array_base, r_array_index, r_bitmap, result, temp1);
    __ jr(RA);

    return start;
  }

#endif // COMPILER2

  // exception handler for upcall stubs
  address generate_upcall_stub_exception_handler() {
    StubCodeMark mark(this, "StubRoutines", "upcall stub exception handler");
    address start = __ pc();

    // Native caller has no idea how to handle exceptions,
    // so we just crash here. Up to callee to catch exceptions.
    __ verify_oop(A0); // return a exception oop in a0
    __ call(CAST_FROM_FN_PTR(address, UpcallLinker::handle_uncaught_exception), relocInfo::runtime_call_type);
    __ should_not_reach_here();

    return start;
  }

  // load Method* target of MethodHandle
  // j_rarg0 = jobject receiver
  // xmethod = Method* result
  address generate_upcall_stub_load_target() {

    StubCodeMark mark(this, "StubRoutines", "upcall_stub_load_target");
    address start = __ pc();

    __ resolve_global_jobject(j_rarg0, SCR2, SCR1);
      // Load target method from receiver
    __ load_heap_oop(Rmethod, Address(j_rarg0, java_lang_invoke_MethodHandle::form_offset()), SCR2, SCR1);
    __ load_heap_oop(Rmethod, Address(Rmethod, java_lang_invoke_LambdaForm::vmentry_offset()), SCR2, SCR1);
    __ load_heap_oop(Rmethod, Address(Rmethod, java_lang_invoke_MemberName::method_offset()), SCR2, SCR1);
    __ access_load_at(T_ADDRESS, IN_HEAP, Rmethod,
                      Address(Rmethod, java_lang_invoke_ResolvedMethodName::vmtarget_offset()),
                      noreg, noreg);
    __ st_d(Rmethod, Address(TREG, JavaThread::callee_target_offset())); // just in case callee is deoptimized

    __ jr(RA);

    return start;
  }

#undef __
#define __ masm->

  class MontgomeryMultiplyGenerator : public MacroAssembler {

    Register Pa_base, Pb_base, Pn_base, Pm_base, inv, Rlen, Rlen2, Ra, Rb, Rm,
      Rn, Iam, Ibn, Rhi_ab, Rlo_ab, Rhi_mn, Rlo_mn, t0, t1, t2, Ri, Rj;

    bool _squaring;

  public:
    MontgomeryMultiplyGenerator (Assembler *as, bool squaring)
      : MacroAssembler(as->code()), _squaring(squaring) {

      // Register allocation

      RegSetIterator<Register> regs = (RegSet::range(A0, T8) \
                                      + RegSet::range(S0, S3)).begin();

      Pa_base = *regs;    // Argument registers:
      if (squaring)
        Pb_base = Pa_base;
      else
        Pb_base = *++regs;
      Pn_base = *++regs;
      Rlen = *++regs;
      inv = *++regs;
      Rlen2 = inv;        // Reuse inv
      Pm_base = *++regs;

                          // Working registers:
      Ra = *++regs;       // The current digit of a, b, n, and m.
      Rb = *++regs;
      Rm = *++regs;
      Rn = *++regs;

      Iam = *++regs;      // Index to the current/next digit of a, b, n, and m.
      Ibn = *++regs;

      t0 = *++regs;       // Three registers which form a
      t1 = *++regs;       // triple-precision accumuator.
      t2 = *++regs;

      Ri = *++regs;       // Inner and outer loop indexes.
      Rj = *++regs;

      Rhi_ab = *++regs;   // Product registers: low and high parts
      Rlo_ab = *++regs;   // of a*b and m*n.
      Rhi_mn = *++regs;
      Rlo_mn = *++regs;
    }

  private:
    void enter() {
      addi_d(SP, SP, -6 * wordSize);
      st_d(FP, SP, 0 * wordSize);
      move(FP, SP);
    }

    void leave() {
      addi_d(T0, FP, 6 * wordSize);
      ld_d(FP, FP, 0 * wordSize);
      move(SP, T0);
    }

    void save_regs() {
      if (!_squaring)
        st_d(Rhi_ab, FP, 5 * wordSize);
      st_d(Rlo_ab, FP, 4 * wordSize);
      st_d(Rhi_mn, FP, 3 * wordSize);
      st_d(Rlo_mn, FP, 2 * wordSize);
      st_d(Pm_base, FP, 1 * wordSize);
    }

    void restore_regs() {
      if (!_squaring)
        ld_d(Rhi_ab, FP, 5 * wordSize);
      ld_d(Rlo_ab, FP, 4 * wordSize);
      ld_d(Rhi_mn, FP, 3 * wordSize);
      ld_d(Rlo_mn, FP, 2 * wordSize);
      ld_d(Pm_base, FP, 1 * wordSize);
    }

    template <typename T>
    void unroll_2(Register count, T block, Register tmp) {
      Label loop, end, odd;
      andi(tmp, count, 1);
      bnez(tmp, odd);
      beqz(count, end);
      align(16);
      bind(loop);
      (this->*block)();
      bind(odd);
      (this->*block)();
      addi_w(count, count, -2);
      blt(R0, count, loop);
      bind(end);
    }

    template <typename T>
    void unroll_2(Register count, T block, Register d, Register s, Register tmp) {
      Label loop, end, odd;
      andi(tmp, count, 1);
      bnez(tmp, odd);
      beqz(count, end);
      align(16);
      bind(loop);
      (this->*block)(d, s, tmp);
      bind(odd);
      (this->*block)(d, s, tmp);
      addi_w(count, count, -2);
      blt(R0, count, loop);
      bind(end);
    }

    void acc(Register Rhi, Register Rlo,
             Register t0, Register t1, Register t2, Register t, Register c) {
      add_d(t0, t0, Rlo);
      OR(t, t1, Rhi);
      sltu(c, t0, Rlo);
      add_d(t1, t1, Rhi);
      add_d(t1, t1, c);
      sltu(c, t1, t);
      add_d(t2, t2, c);
    }

    void pre1(Register i) {
      block_comment("pre1");
      // Iam = 0;
      // Ibn = i;

      slli_w(Ibn, i, LogBytesPerWord);

      // Ra = Pa_base[Iam];
      // Rb = Pb_base[Ibn];
      // Rm = Pm_base[Iam];
      // Rn = Pn_base[Ibn];

      ld_d(Ra, Pa_base, 0);
      ldx_d(Rb, Pb_base, Ibn);
      ld_d(Rm, Pm_base, 0);
      ldx_d(Rn, Pn_base, Ibn);

      move(Iam, R0);

      // Zero the m*n result.
      move(Rhi_mn, R0);
      move(Rlo_mn, R0);
    }

    // The core multiply-accumulate step of a Montgomery
    // multiplication.  The idea is to schedule operations as a
    // pipeline so that instructions with long latencies (loads and
    // multiplies) have time to complete before their results are
    // used.  This most benefits in-order implementations of the
    // architecture but out-of-order ones also benefit.
    void step() {
      block_comment("step");
      // MACC(Ra, Rb, t0, t1, t2);
      // Ra = Pa_base[++Iam];
      // Rb = Pb_base[--Ibn];
      addi_d(Iam, Iam, wordSize);
      addi_d(Ibn, Ibn, -wordSize);
      mul_d(Rlo_ab, Ra, Rb);
      mulh_du(Rhi_ab, Ra, Rb);
      acc(Rhi_mn, Rlo_mn, t0, t1, t2, Ra, Rb); // The pending m*n from the
                                               // previous iteration.
      ldx_d(Ra, Pa_base, Iam);
      ldx_d(Rb, Pb_base, Ibn);

      // MACC(Rm, Rn, t0, t1, t2);
      // Rm = Pm_base[Iam];
      // Rn = Pn_base[Ibn];
      mul_d(Rlo_mn, Rm, Rn);
      mulh_du(Rhi_mn, Rm, Rn);
      acc(Rhi_ab, Rlo_ab, t0, t1, t2, Rm, Rn);
      ldx_d(Rm, Pm_base, Iam);
      ldx_d(Rn, Pn_base, Ibn);
    }

    void post1() {
      block_comment("post1");

      // MACC(Ra, Rb, t0, t1, t2);
      mul_d(Rlo_ab, Ra, Rb);
      mulh_du(Rhi_ab, Ra, Rb);
      acc(Rhi_mn, Rlo_mn, t0, t1, t2, Ra, Rb);  // The pending m*n
      acc(Rhi_ab, Rlo_ab, t0, t1, t2, Ra, Rb);

      // Pm_base[Iam] = Rm = t0 * inv;
      mul_d(Rm, t0, inv);
      stx_d(Rm, Pm_base, Iam);

      // MACC(Rm, Rn, t0, t1, t2);
      // t0 = t1; t1 = t2; t2 = 0;
      mulh_du(Rhi_mn, Rm, Rn);

#ifndef PRODUCT
      // assert(m[i] * n[0] + t0 == 0, "broken Montgomery multiply");
      {
        mul_d(Rlo_mn, Rm, Rn);
        add_d(Rlo_mn, t0, Rlo_mn);
        Label ok;
        beqz(Rlo_mn, ok); {
          stop("broken Montgomery multiply");
        } bind(ok);
      }
#endif

      // We have very carefully set things up so that
      // m[i]*n[0] + t0 == 0 (mod b), so we don't have to calculate
      // the lower half of Rm * Rn because we know the result already:
      // it must be -t0.  t0 + (-t0) must generate a carry iff
      // t0 != 0.  So, rather than do a mul and an adds we just set
      // the carry flag iff t0 is nonzero.
      //
      // mul_d(Rlo_mn, Rm, Rn);
      // add_d(t0, t0, Rlo_mn);
      OR(Ra, t1, Rhi_mn);
      sltu(Rb, R0, t0);
      add_d(t0, t1, Rhi_mn);
      add_d(t0, t0, Rb);
      sltu(Rb, t0, Ra);
      add_d(t1, t2, Rb);
      move(t2, R0);
    }

    void pre2(Register i, Register len) {
      block_comment("pre2");

      // Rj == i-len
      sub_w(Rj, i, len);

      // Iam = i - len;
      // Ibn = len;
      slli_w(Iam, Rj, LogBytesPerWord);
      slli_w(Ibn, len, LogBytesPerWord);

      // Ra = Pa_base[++Iam];
      // Rb = Pb_base[--Ibn];
      // Rm = Pm_base[++Iam];
      // Rn = Pn_base[--Ibn];
      addi_d(Iam, Iam, wordSize);
      addi_d(Ibn, Ibn, -wordSize);

      ldx_d(Ra, Pa_base, Iam);
      ldx_d(Rb, Pb_base, Ibn);
      ldx_d(Rm, Pm_base, Iam);
      ldx_d(Rn, Pn_base, Ibn);

      move(Rhi_mn, R0);
      move(Rlo_mn, R0);
    }

    void post2(Register i, Register len) {
      block_comment("post2");

      sub_w(Rj, i, len);
      alsl_d(Iam, Rj, Pm_base, LogBytesPerWord - 1);

      add_d(t0, t0, Rlo_mn); // The pending m*n, low part

      // As soon as we know the least significant digit of our result,
      // store it.
      // Pm_base[i-len] = t0;
      st_d(t0, Iam, 0);

      // t0 = t1; t1 = t2; t2 = 0;
      OR(Ra, t1, Rhi_mn);
      sltu(Rb, t0, Rlo_mn);
      add_d(t0, t1, Rhi_mn); // The pending m*n, high part
      add_d(t0, t0, Rb);
      sltu(Rb, t0, Ra);
      add_d(t1, t2, Rb);
      move(t2, R0);
    }

    // A carry in t0 after Montgomery multiplication means that we
    // should subtract multiples of n from our result in m.  We'll
    // keep doing that until there is no carry.
    void normalize(Register len) {
      block_comment("normalize");
      // while (t0)
      //   t0 = sub(Pm_base, Pn_base, t0, len);
      Label loop, post, again;
      Register cnt = t1, i = t2, b = Ra, t = Rb; // Re-use registers; we're done with them now
      beqz(t0, post); {
        bind(again); {
          move(i, R0);
          move(b, R0);
          slli_w(cnt, len, LogBytesPerWord);
          align(16);
          bind(loop); {
            ldx_d(Rm, Pm_base, i);
            ldx_d(Rn, Pn_base, i);
            sltu(t, Rm, b);
            sub_d(Rm, Rm, b);
            sltu(b, Rm, Rn);
            sub_d(Rm, Rm, Rn);
            OR(b, b, t);
            stx_d(Rm, Pm_base, i);
            addi_w(i, i, BytesPerWord);
          } blt(i, cnt, loop);
          sub_d(t0, t0, b);
        } bnez(t0, again);
      } bind(post);
    }

    // Move memory at s to d, reversing words.
    //    Increments d to end of copied memory
    //    Destroys tmp1, tmp2, tmp3
    //    Preserves len
    //    Leaves s pointing to the address which was in d at start
    void reverse(Register d, Register s, Register len, Register tmp1, Register tmp2) {
      assert(tmp1->encoding() < S0->encoding(), "register corruption");
      assert(tmp2->encoding() < S0->encoding(), "register corruption");

      alsl_d(s, len, s, LogBytesPerWord - 1);
      move(tmp1, len);
      unroll_2(tmp1, &MontgomeryMultiplyGenerator::reverse1, d, s, tmp2);
      slli_w(s, len, LogBytesPerWord);
      sub_d(s, d, s);
    }

    // where
    void reverse1(Register d, Register s, Register tmp) {
      ld_d(tmp, s, -wordSize);
      addi_d(s, s, -wordSize);
      addi_d(d, d, wordSize);
      rotri_d(tmp, tmp, 32);
      st_d(tmp, d, -wordSize);
    }

  public:
    /**
     * Fast Montgomery multiplication.  The derivation of the
     * algorithm is in A Cryptographic Library for the Motorola
     * DSP56000, Dusse and Kaliski, Proc. EUROCRYPT 90, pp. 230-237.
     *
     * Arguments:
     *
     * Inputs for multiplication:
     *   A0   - int array elements a
     *   A1   - int array elements b
     *   A2   - int array elements n (the modulus)
     *   A3   - int length
     *   A4   - int inv
     *   A5   - int array elements m (the result)
     *
     * Inputs for squaring:
     *   A0   - int array elements a
     *   A1   - int array elements n (the modulus)
     *   A2   - int length
     *   A3   - int inv
     *   A4   - int array elements m (the result)
     *
     */
    address generate_multiply() {
      Label argh, nothing;
      bind(argh);
      stop("MontgomeryMultiply total_allocation must be <= 8192");

      align(CodeEntryAlignment);
      address entry = pc();

      beqz(Rlen, nothing);

      enter();

      // Make room.
      sltui(Ra, Rlen, 513);
      beqz(Ra, argh);
      slli_w(Ra, Rlen, exact_log2(4 * sizeof (jint)));
      sub_d(Ra, SP, Ra);

      srli_w(Rlen, Rlen, 1); // length in longwords = len/2

      {
        // Copy input args, reversing as we go.  We use Ra as a
        // temporary variable.
        reverse(Ra, Pa_base, Rlen, t0, t1);
        if (!_squaring)
          reverse(Ra, Pb_base, Rlen, t0, t1);
        reverse(Ra, Pn_base, Rlen, t0, t1);
      }

      // Push all call-saved registers and also Pm_base which we'll need
      // at the end.
      save_regs();

#ifndef PRODUCT
      // assert(inv * n[0] == -1UL, "broken inverse in Montgomery multiply");
      {
        ld_d(Rn, Pn_base, 0);
        li(t0, -1);
        mul_d(Rlo_mn, Rn, inv);
        Label ok;
        beq(Rlo_mn, t0, ok); {
          stop("broken inverse in Montgomery multiply");
        } bind(ok);
      }
#endif

      move(Pm_base, Ra);

      move(t0, R0);
      move(t1, R0);
      move(t2, R0);

      block_comment("for (int i = 0; i < len; i++) {");
      move(Ri, R0); {
        Label loop, end;
        bge(Ri, Rlen, end);

        bind(loop);
        pre1(Ri);

        block_comment("  for (j = i; j; j--) {"); {
          move(Rj, Ri);
          unroll_2(Rj, &MontgomeryMultiplyGenerator::step, Rlo_ab);
        } block_comment("  } // j");

        post1();
        addi_w(Ri, Ri, 1);
        blt(Ri, Rlen, loop);
        bind(end);
        block_comment("} // i");
      }

      block_comment("for (int i = len; i < 2*len; i++) {");
      move(Ri, Rlen);
      slli_w(Rlen2, Rlen, 1); {
        Label loop, end;
        bge(Ri, Rlen2, end);

        bind(loop);
        pre2(Ri, Rlen);

        block_comment("  for (j = len*2-i-1; j; j--) {"); {
          sub_w(Rj, Rlen2, Ri);
          addi_w(Rj, Rj, -1);
          unroll_2(Rj, &MontgomeryMultiplyGenerator::step, Rlo_ab);
        } block_comment("  } // j");

        post2(Ri, Rlen);
        addi_w(Ri, Ri, 1);
        blt(Ri, Rlen2, loop);
        bind(end);
      }
      block_comment("} // i");

      normalize(Rlen);

      move(Ra, Pm_base);  // Save Pm_base in Ra
      restore_regs();  // Restore caller's Pm_base

      // Copy our result into caller's Pm_base
      reverse(Pm_base, Ra, Rlen, t0, t1);

      leave();
      bind(nothing);
      jr(RA);

      return entry;
    }
    // In C, approximately:

    // void
    // montgomery_multiply(unsigned long Pa_base[], unsigned long Pb_base[],
    //                     unsigned long Pn_base[], unsigned long Pm_base[],
    //                     unsigned long inv, int len) {
    //   unsigned long t0 = 0, t1 = 0, t2 = 0; // Triple-precision accumulator
    //   unsigned long Ra, Rb, Rn, Rm;
    //   int i, Iam, Ibn;

    //   assert(inv * Pn_base[0] == -1UL, "broken inverse in Montgomery multiply");

    //   for (i = 0; i < len; i++) {
    //     int j;

    //     Iam = 0;
    //     Ibn = i;

    //     Ra = Pa_base[Iam];
    //     Rb = Pb_base[Iam];
    //     Rm = Pm_base[Ibn];
    //     Rn = Pn_base[Ibn];

    //     int iters = i;
    //     for (j = 0; iters--; j++) {
    //       assert(Ra == Pa_base[j] && Rb == Pb_base[i-j], "must be");
    //       MACC(Ra, Rb, t0, t1, t2);
    //       Ra = Pa_base[++Iam];
    //       Rb = pb_base[--Ibn];
    //       assert(Rm == Pm_base[j] && Rn == Pn_base[i-j], "must be");
    //       MACC(Rm, Rn, t0, t1, t2);
    //       Rm = Pm_base[++Iam];
    //       Rn = Pn_base[--Ibn];
    //     }

    //     assert(Ra == Pa_base[i] && Rb == Pb_base[0], "must be");
    //     MACC(Ra, Rb, t0, t1, t2);
    //     Pm_base[Iam] = Rm = t0 * inv;
    //     assert(Rm == Pm_base[i] && Rn == Pn_base[0], "must be");
    //     MACC(Rm, Rn, t0, t1, t2);

    //     assert(t0 == 0, "broken Montgomery multiply");

    //     t0 = t1; t1 = t2; t2 = 0;
    //   }

    //   for (i = len; i < 2*len; i++) {
    //     int j;

    //     Iam = i - len;
    //     Ibn = len;

    //     Ra = Pa_base[++Iam];
    //     Rb = Pb_base[--Ibn];
    //     Rm = Pm_base[++Iam];
    //     Rn = Pn_base[--Ibn];

    //     int iters = len*2-i-1;
    //     for (j = i-len+1; iters--; j++) {
    //       assert(Ra == Pa_base[j] && Rb == Pb_base[i-j], "must be");
    //       MACC(Ra, Rb, t0, t1, t2);
    //       Ra = Pa_base[++Iam];
    //       Rb = Pb_base[--Ibn];
    //       assert(Rm == Pm_base[j] && Rn == Pn_base[i-j], "must be");
    //       MACC(Rm, Rn, t0, t1, t2);
    //       Rm = Pm_base[++Iam];
    //       Rn = Pn_base[--Ibn];
    //     }

    //     Pm_base[i-len] = t0;
    //     t0 = t1; t1 = t2; t2 = 0;
    //   }

    //   while (t0)
    //     t0 = sub(Pm_base, Pn_base, t0, len);
    // }
  };

  // Initialization
  void generate_initial_stubs() {
    // Generates all stubs and initializes the entry points

    //-------------------------------------------------------------
    //-----------------------------------------------------------
    // entry points that exist in all platforms
    // Note: This is code that could be shared among different platforms - however the benefit seems to be smaller
    // than the disadvantage of having a much more complicated generator structure.
    // See also comment in stubRoutines.hpp.
    StubRoutines::_forward_exception_entry = generate_forward_exception();
    StubRoutines::_call_stub_entry = generate_call_stub(StubRoutines::_call_stub_return_address);
    // is referenced by megamorphic call
    StubRoutines::_catch_exception_entry = generate_catch_exception();

    // Initialize table for copy memory (arraycopy) check.
    if (UnsafeMemoryAccess::_table == nullptr) {
      UnsafeMemoryAccess::create_table(8 + 4 ZGC_ONLY(+ (UseZGC ? 14 : 0))); // 8 for copyMemory; 4 for setMemory
    }

    if (UseCRC32Intrinsics) {
      // set table address before stub generation which use it
      StubRoutines::_crc_table_adr = (address)StubRoutines::la::_crc_table;
      StubRoutines::_updateBytesCRC32 = generate_updateBytesCRC32();
    }

    if (UseCRC32CIntrinsics) {
      StubRoutines::_updateBytesCRC32C = generate_updateBytesCRC32C();
    }
 }

  void generate_continuation_stubs() {
    // Continuation stubs:
    StubRoutines::_cont_thaw             = generate_cont_thaw();
    StubRoutines::_cont_returnBarrier    = generate_cont_returnBarrier();
    StubRoutines::_cont_returnBarrierExc = generate_cont_returnBarrier_exception();
    StubRoutines::_cont_preempt_stub     = generate_cont_preempt_stub();
  }

  void generate_final_stubs() {
    // Generates all stubs and initializes the entry points

    // support for verify_oop (must happen after universe_init)
    if (VerifyOops) {
      StubRoutines::_verify_oop_subroutine_entry   = generate_verify_oop();
    }

    // arraycopy stubs used by compilers
    generate_arraycopy_stubs();

    if (UseLSX && vmIntrinsics::is_intrinsic_available(vmIntrinsics::_dsin)) {
      StubRoutines::_dsin = generate_dsin_dcos(/* isCos = */ false);
    }

    if (UseLSX && vmIntrinsics::is_intrinsic_available(vmIntrinsics::_dcos)) {
      StubRoutines::_dcos = generate_dsin_dcos(/* isCos = */ true);
    }

    BarrierSetNMethod* bs_nm = BarrierSet::barrier_set()->barrier_set_nmethod();
    if (bs_nm != nullptr) {
      StubRoutines::_method_entry_barrier = generate_method_entry_barrier();
    }

#ifdef COMPILER2
    if (UseSecondarySupersTable) {
      StubRoutines::_lookup_secondary_supers_table_slow_path_stub = generate_lookup_secondary_supers_table_slow_path_stub();
      if (!InlineSecondarySupersTest) {
        for (int slot = 0; slot < Klass::SECONDARY_SUPERS_TABLE_SIZE; slot++) {
          StubRoutines::_lookup_secondary_supers_table_stubs[slot]
            = generate_lookup_secondary_supers_table_stub(slot);
        }
      }
    }
#endif // COMPILER2

    StubRoutines::_upcall_stub_exception_handler = generate_upcall_stub_exception_handler();
    StubRoutines::_upcall_stub_load_target = generate_upcall_stub_load_target();
  }

  void generate_compiler_stubs() {
#if COMPILER2_OR_JVMCI
#ifdef COMPILER2
    if (UseMulAddIntrinsic) {
      StubRoutines::_mulAdd = generate_mulAdd();
    }

    if (UseMontgomeryMultiplyIntrinsic) {
      StubCodeMark mark(this, "StubRoutines", "montgomeryMultiply");
      MontgomeryMultiplyGenerator g(_masm, false /* squaring */);
      StubRoutines::_montgomeryMultiply = g.generate_multiply();
    }

    if (UseMontgomerySquareIntrinsic) {
      StubCodeMark mark(this, "StubRoutines", "montgomerySquare");
      MontgomeryMultiplyGenerator g(_masm, true /* squaring */);
      // We use generate_multiply() rather than generate_square()
      // because it's faster for the sizes of modulus we care about.
      StubRoutines::_montgomerySquare = g.generate_multiply();
    }

    if (UsePoly1305Intrinsics) {
      StubRoutines::_poly1305_processBlocks = generate_poly1305_processBlocks();
    }

    if (UseBigIntegerShiftIntrinsic) {
      StubRoutines::_bigIntegerLeftShiftWorker = generate_bigIntegerLeftShift();
      StubRoutines::_bigIntegerRightShiftWorker = generate_bigIntegerRightShift();
    }
#endif

    StubRoutines::la::_vector_iota_indices = generate_iota_indices("iota_indices");

    if (UseAESIntrinsics) {
      StubRoutines::_aescrypt_encryptBlock = generate_aescrypt_encryptBlock(false);
      StubRoutines::_aescrypt_decryptBlock = generate_aescrypt_decryptBlock(false);
      StubRoutines::_cipherBlockChaining_encryptAESCrypt = generate_aescrypt_encryptBlock(true);
      StubRoutines::_cipherBlockChaining_decryptAESCrypt = generate_aescrypt_decryptBlock(true);
    }

    if (UseMD5Intrinsics) {
      generate_md5_implCompress("md5_implCompress", StubRoutines::_md5_implCompress, StubRoutines::_md5_implCompressMB);
    }

    if (UseSHA1Intrinsics) {
      generate_sha1_implCompress("sha1_implCompress", StubRoutines::_sha1_implCompress, StubRoutines::_sha1_implCompressMB);
    }

    if (UseSHA256Intrinsics) {
      generate_sha256_implCompress("sha256_implCompress", StubRoutines::_sha256_implCompress, StubRoutines::_sha256_implCompressMB);
    }

    if (UseChaCha20Intrinsics) {
      StubRoutines::_chacha20Block = generate_chacha20Block_blockpar();
    }

    generate_string_indexof_stubs();

#endif // COMPILER2_OR_JVMCI
  }

 public:
  StubGenerator(CodeBuffer* code, StubsKind kind) : StubCodeGenerator(code) {
    switch(kind) {
    case Initial_stubs:
      generate_initial_stubs();
      break;
     case Continuation_stubs:
      generate_continuation_stubs();
      break;
    case Compiler_stubs:
      generate_compiler_stubs();
      break;
    case Final_stubs:
      generate_final_stubs();
      break;
    default:
      fatal("unexpected stubs kind: %d", kind);
      break;
    };
  }
}; // end class declaration

void StubGenerator_generate(CodeBuffer* code, StubCodeGenerator::StubsKind kind) {
  StubGenerator g(code, kind);
}
