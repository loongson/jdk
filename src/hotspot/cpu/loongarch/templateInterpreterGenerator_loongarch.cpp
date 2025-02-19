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
#include "classfile/javaClasses.hpp"
#include "compiler/disassembler.hpp"
#include "gc/shared/barrierSetAssembler.hpp"
#include "interpreter/bytecodeHistogram.hpp"
#include "interpreter/interp_masm.hpp"
#include "interpreter/interpreter.hpp"
#include "interpreter/interpreterRuntime.hpp"
#include "interpreter/templateInterpreterGenerator.hpp"
#include "interpreter/templateTable.hpp"
#include "oops/arrayOop.hpp"
#include "oops/method.hpp"
#include "oops/methodCounters.hpp"
#include "oops/methodData.hpp"
#include "oops/oop.inline.hpp"
#include "oops/resolvedIndyEntry.hpp"
#include "oops/resolvedMethodEntry.hpp"
#include "prims/jvmtiExport.hpp"
#include "prims/jvmtiThreadState.hpp"
#include "runtime/arguments.hpp"
#include "runtime/deoptimization.hpp"
#include "runtime/frame.inline.hpp"
#include "runtime/globals.hpp"
#include "runtime/jniHandles.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/stubRoutines.hpp"
#include "runtime/synchronizer.hpp"
#include "runtime/timer.hpp"
#include "runtime/vframeArray.hpp"
#include "utilities/debug.hpp"

#define __ Disassembler::hook<InterpreterMacroAssembler>(__FILE__, __LINE__, _masm)->

int TemplateInterpreter::InterpreterCodeSize = 500 * K;

#ifdef PRODUCT
#define BLOCK_COMMENT(str) /* nothing */
#else
#define BLOCK_COMMENT(str) __ block_comment(str)
#endif

address TemplateInterpreterGenerator::generate_slow_signature_handler() {
  address entry = __ pc();
  // Rmethod: method
  // LVP: pointer to locals
  // A3: first stack arg
  __ move(A3, SP);
  __ addi_d(SP, SP, -18 * wordSize);
  __ st_d(RA, SP, 0);
  __ call_VM(noreg,
             CAST_FROM_FN_PTR(address,
                              InterpreterRuntime::slow_signature_handler),
             Rmethod, LVP, A3);

  // V0: result handler

  // Stack layout:
  //        ...
  //     18 stack arg0   <--- old sp
  //     17 floatReg arg7
  //        ...
  //     10 floatReg arg0
  //      9 float/double identifiers
  //      8 IntReg arg7
  //        ...
  //      2 IntReg arg1
  //      1 aligned slot
  // SP:  0 return address

  // Do FPU first so we can use A3 as temp
  __ ld_d(A3, Address(SP, 9 * wordSize)); // float/double identifiers

  for (int i= 0; i < Argument::n_float_register_parameters_c; i++) {
    FloatRegister floatreg = as_FloatRegister(i + FA0->encoding());
    Label isdouble, done;

    __ test_bit(AT, A3, i);
    __ bnez(AT, isdouble);
    __ fld_s(floatreg, SP, (10 + i) * wordSize);
    __ b(done);
    __ bind(isdouble);
    __ fld_d(floatreg, SP, (10 + i) * wordSize);
    __ bind(done);
  }

  // A0 is for env.
  // If the mothed is not static, A1 will be corrected in generate_native_entry.
  for (int i= 1; i < Argument::n_int_register_parameters_c; i++) {
    Register reg = as_Register(i + A0->encoding());
    __ ld_d(reg, SP, (1 + i) * wordSize);
  }

  // A0/V0 contains the result from the call of
  // InterpreterRuntime::slow_signature_handler so we don't touch it
  // here.  It will be loaded with the JNIEnv* later.
  __ ld_d(RA, SP, 0);
  __ addi_d(SP, SP, 18 * wordSize);
  __ jr(RA);
  return entry;
}

/**
 * Method entry for static native methods:
 *   int java.util.zip.CRC32.update(int crc, int b)
 */
address TemplateInterpreterGenerator::generate_CRC32_update_entry() {
  assert(UseCRC32Intrinsics, "this intrinsic is not supported");
  address entry = __ pc();

  // rmethod: Method*
  // Rsender: senderSP must preserved for slow path
  // SP: args

  Label slow_path;
  // If we need a safepoint check, generate full interpreter entry.
  __ safepoint_poll(slow_path, TREG, false /* at_return */, false /* acquire */, false /* in_nmethod */);

  // We don't generate local frame and don't align stack because
  // we call stub code and there is no safepoint on this path.

  const Register crc = A0;  // crc
  const Register val = A1;  // source java byte value
  const Register tbl = A2;  // scratch

  // Arguments are reversed on java expression stack
  __ ld_w(val, SP, 0);              // byte value
  __ ld_w(crc, SP, wordSize);       // Initial CRC

  __ li(tbl, (long)StubRoutines::crc_table_addr());

  __ nor(crc, crc, R0); // ~crc
  __ update_byte_crc32(crc, val, tbl);
  __ nor(crc, crc, R0); // ~crc

  // restore caller SP
  __ move(SP, Rsender);
  __ jr(RA);

  // generate a vanilla native entry as the slow path
  __ bind(slow_path);
  __ jump_to_entry(Interpreter::entry_for_kind(Interpreter::native));
  return entry;
}

/**
 * Method entry for static native methods:
 *   int java.util.zip.CRC32.updateBytes(int crc, byte[] b, int off, int len)
 *   int java.util.zip.CRC32.updateByteBuffer(int crc, long buf, int off, int len)
 */
address TemplateInterpreterGenerator::generate_CRC32_updateBytes_entry(AbstractInterpreter::MethodKind kind) {
  assert(UseCRC32Intrinsics, "this intrinsic is not supported");
  address entry = __ pc();

  // rmethod: Method*
  // Rsender: senderSP must preserved for slow path
  // SP: args

  Label slow_path;
  // If we need a safepoint check, generate full interpreter entry.
  __ safepoint_poll(slow_path, TREG, false /* at_return */, false /* acquire */, false /* in_nmethod */);

  // We don't generate local frame and don't align stack because
  // we call stub code and there is no safepoint on this path.

  const Register crc = A0;  // crc
  const Register buf = A1;  // source java byte array address
  const Register len = A2;  // length
  const Register tmp = A3;

  const Register off = len; // offset (never overlaps with 'len')

  // Arguments are reversed on java expression stack
  // Calculate address of start element
  __ ld_w(off, SP, wordSize);       // int offset
  __ ld_d(buf, SP, 2 * wordSize);   // byte[] buf | long buf
  __ add_d(buf, buf, off);          // + offset
  if (kind == Interpreter::java_util_zip_CRC32_updateByteBuffer) {
    __ ld_w(crc, SP, 4 * wordSize); // long crc
  } else {
    __ addi_d(buf, buf, arrayOopDesc::base_offset_in_bytes(T_BYTE)); // + header size
    __ ld_w(crc, SP, 3 * wordSize); // long crc
  }

  // Can now load 'len' since we're finished with 'off'
  __ ld_w(len, SP, 0); // length

  __ kernel_crc32(crc, buf, len, tmp);

  // restore caller SP
  __ move(SP, Rsender);
  __ jr(RA);

  // generate a vanilla native entry as the slow path
  __ bind(slow_path);
  __ jump_to_entry(Interpreter::entry_for_kind(Interpreter::native));
  return entry;
}

/**
 * Method entry for intrinsic-candidate (non-native) methods:
 *   int java.util.zip.CRC32C.updateBytes(int crc, byte[] b, int off, int end)
 *   int java.util.zip.CRC32C.updateDirectByteBuffer(int crc, long buf, int off, int end)
 * Unlike CRC32, CRC32C does not have any methods marked as native
 * CRC32C also uses an "end" variable instead of the length variable CRC32 uses
 */
address TemplateInterpreterGenerator::generate_CRC32C_updateBytes_entry(AbstractInterpreter::MethodKind kind) {
  assert(UseCRC32CIntrinsics, "this intrinsic is not supported");
  address entry = __ pc();

  const Register crc = A0; // initial crc
  const Register buf = A1; // source java byte array address
  const Register len = A2; // len argument to the kernel
  const Register tmp = A3;

  const Register end = len; // index of last element to process
  const Register off = crc; // offset

  __ ld_w(end, SP, 0);              // int end
  __ ld_w(off, SP, wordSize);       // int offset
  __ sub_w(len, end, off);          // calculate length
  __ ld_d(buf, SP, 2 * wordSize);   // byte[] buf | long buf
  __ add_d(buf, buf, off);          // + offset
  if (kind == Interpreter::java_util_zip_CRC32C_updateDirectByteBuffer) {
    __ ld_w(crc, SP, 4 * wordSize); // int crc
  } else {
    __ addi_d(buf, buf, arrayOopDesc::base_offset_in_bytes(T_BYTE)); // + header size
    __ ld_w(crc, SP, 3 * wordSize); // int crc
  }

  __ kernel_crc32c(crc, buf, len, tmp);

  // restore caller SP
  __ move(SP, Rsender);
  __ jr(RA);

  return entry;
}

//
// Various method entries
//

address TemplateInterpreterGenerator::generate_math_entry(AbstractInterpreter::MethodKind kind) {
  // These don't need a safepoint check because they aren't virtually
  // callable. We won't enter these intrinsics from compiled code.
  // If in the future we added an intrinsic which was virtually callable
  // we'd have to worry about how to safepoint so that this code is used.

  // mathematical functions inlined by compiler
  // (interpreter must provide identical implementation
  // in order to avoid monotonicity bugs when switching
  // from interpreter to compiler in the middle of some
  // computation)
  //
  // stack:
  //        [ arg ] <-- sp
  //        [ arg ]
  // retaddr in ra

  address entry_point = nullptr;
  switch (kind) {
  case Interpreter::java_lang_math_abs:
    entry_point = __ pc();
    __ fld_d(FA0, SP, 0);
    __ fabs_d(F0, FA0);
    __ move(SP, Rsender);
    break;
  case Interpreter::java_lang_math_sqrt:
    entry_point = __ pc();
    __ fld_d(FA0, SP, 0);
    __ fsqrt_d(F0, FA0);
    __ move(SP, Rsender);
    break;
  case Interpreter::java_lang_math_sin :
  case Interpreter::java_lang_math_cos :
  case Interpreter::java_lang_math_tan :
  case Interpreter::java_lang_math_log :
  case Interpreter::java_lang_math_log10 :
  case Interpreter::java_lang_math_exp :
    entry_point = __ pc();
    __ fld_d(FA0, SP, 0);
    __ move(SP, Rsender);
    __ movgr2fr_d(FS0, RA);
    __ movgr2fr_d(FS1, SP);
    __ bstrins_d(SP, R0, exact_log2(StackAlignmentInBytes) - 1, 0);
    generate_transcendental_entry(kind, 1);
    __ movfr2gr_d(SP, FS1);
    __ movfr2gr_d(RA, FS0);
    break;
  case Interpreter::java_lang_math_pow :
    entry_point = __ pc();
    __ fld_d(FA0, SP, 2 * Interpreter::stackElementSize);
    __ fld_d(FA1, SP, 0);
    __ move(SP, Rsender);
    __ movgr2fr_d(FS0, RA);
    __ movgr2fr_d(FS1, SP);
    __ bstrins_d(SP, R0, exact_log2(StackAlignmentInBytes) - 1, 0);
    generate_transcendental_entry(kind, 2);
    __ movfr2gr_d(SP, FS1);
    __ movfr2gr_d(RA, FS0);
    break;
  case Interpreter::java_lang_math_fmaD :
    if (UseFMA) {
      entry_point = __ pc();
      __ fld_d(FA0, SP, 4 * Interpreter::stackElementSize);
      __ fld_d(FA1, SP, 2 * Interpreter::stackElementSize);
      __ fld_d(FA2, SP, 0);
      __ fmadd_d(F0, FA0, FA1, FA2);
      __ move(SP, Rsender);
    }
    break;
  case Interpreter::java_lang_math_fmaF :
    if (UseFMA) {
      entry_point = __ pc();
      __ fld_s(FA0, SP, 2 * Interpreter::stackElementSize);
      __ fld_s(FA1, SP, Interpreter::stackElementSize);
      __ fld_s(FA2, SP, 0);
      __ fmadd_s(F0, FA0, FA1, FA2);
      __ move(SP, Rsender);
    }
    break;
  default:
    ;
  }
  if (entry_point) {
    __ jr(RA);
  }

  return entry_point;
}

/**
 * Method entry for static method:
 *    java.lang.Float.float16ToFloat(short floatBinary16)
 */
address TemplateInterpreterGenerator::generate_Float_float16ToFloat_entry() {
  assert(VM_Version::supports_float16(), "this intrinsic is not supported");
  address entry_point = __ pc();
  __ ld_w(A0, SP, 0);
  __ flt16_to_flt(F0, A0, F1);
  __ move(SP, Rsender); // Restore caller's SP
  __ jr(RA);
  return entry_point;
}

/**
 * Method entry for static method:
 *    java.lang.Float.floatToFloat16(float value)
 */
address TemplateInterpreterGenerator::generate_Float_floatToFloat16_entry() {
  assert(VM_Version::supports_float16(), "this intrinsic is not supported");
  address entry_point = __ pc();
  __ fld_s(F0, SP, 0);
  __ flt_to_flt16(A0, F0, F1);
  __ move(SP, Rsender); // Restore caller's SP
  __ jr(RA);
  return entry_point;
}

// Not supported
address TemplateInterpreterGenerator::generate_Float_intBitsToFloat_entry() { return nullptr; }
address TemplateInterpreterGenerator::generate_Float_floatToRawIntBits_entry() { return nullptr; }
address TemplateInterpreterGenerator::generate_Double_longBitsToDouble_entry() { return nullptr; }
address TemplateInterpreterGenerator::generate_Double_doubleToRawLongBits_entry() { return nullptr; }

// Method entry for java.lang.Thread.currentThread
address TemplateInterpreterGenerator::generate_currentThread() {

  address entry_point = __ pc();

  __ ld_d(A0, Address(TREG, JavaThread::vthread_offset()));
  __ resolve_oop_handle(A0, SCR2, SCR1);
  __ jr(RA);

  return entry_point;
}

  // double trigonometrics and transcendentals
  // static jdouble dsin(jdouble x);
  // static jdouble dcos(jdouble x);
  // static jdouble dtan(jdouble x);
  // static jdouble dlog(jdouble x);
  // static jdouble dlog10(jdouble x);
  // static jdouble dexp(jdouble x);
  // static jdouble dpow(jdouble x, jdouble y);

void TemplateInterpreterGenerator::generate_transcendental_entry(AbstractInterpreter::MethodKind kind, int fpargs) {
  address fn;
  switch (kind) {
  case Interpreter::java_lang_math_sin :
    if (StubRoutines::dsin() == nullptr) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dsin);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dsin());
    }
    break;
  case Interpreter::java_lang_math_cos :
    if (StubRoutines::dcos() == nullptr) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dcos);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dcos());
    }
    break;
  case Interpreter::java_lang_math_tan :
    if (StubRoutines::dtan() == nullptr) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dtan);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dtan());
    }
    break;
  case Interpreter::java_lang_math_log :
    if (StubRoutines::dlog() == nullptr) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dlog);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dlog());
    }
    break;
  case Interpreter::java_lang_math_log10 :
    if (StubRoutines::dlog10() == nullptr) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dlog10);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dlog10());
    }
    break;
  case Interpreter::java_lang_math_exp :
    if (StubRoutines::dexp() == nullptr) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dexp);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dexp());
    }
    break;
  case Interpreter::java_lang_math_pow :
    if (StubRoutines::dpow() == nullptr) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dpow);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dpow());
    }
    break;
  default:
    ShouldNotReachHere();
    fn = nullptr;  // unreachable
  }
  __ li(T4, fn);
  __ jalr(T4);
}

// Abstract method entry
// Attempt to execute abstract method. Throw exception
address TemplateInterpreterGenerator::generate_abstract_entry(void) {

  // Rmethod: Method*
  // V0: receiver (unused)
  // Rsender : sender 's sp
  address entry_point = __ pc();

  // abstract method entry
  // throw exception
  // adjust stack to what a normal return would do
  __ empty_expression_stack();
  __ restore_bcp();
  __ restore_locals();
  __ call_VM(noreg, CAST_FROM_FN_PTR(address, InterpreterRuntime::throw_AbstractMethodErrorWithMethod), Rmethod);
  // the call_VM checks for exception, so we should never return here.
  __ should_not_reach_here();

  return entry_point;
}


const int method_offset = frame::interpreter_frame_method_offset * wordSize;

//-----------------------------------------------------------------------------

address TemplateInterpreterGenerator::generate_StackOverflowError_handler() {
  address entry = __ pc();

#ifdef ASSERT
  {
    Label L;
    __ ld_d(T1, FP, frame::interpreter_frame_monitor_block_top_offset * wordSize);
    __ alsl_d(T1, T1, FP, LogBytesPerWord-1);
    // maximal sp for current fp (stack grows negative)
    // check if frame is complete
    __ bge(T1, SP, L);
    __ stop("interpreter frame not set up");
    __ bind(L);
  }
#endif // ASSERT
  // Restore bcp under the assumption that the current frame is still
  // interpreted
  __ restore_bcp();

  // expression stack must be empty before entering the VM if an
  // exception happened
  __ empty_expression_stack();
  // throw exception
  __ call_VM(NOREG, CAST_FROM_FN_PTR(address, InterpreterRuntime::throw_StackOverflowError));
  return entry;
}

address TemplateInterpreterGenerator::generate_ArrayIndexOutOfBounds_handler() {
  address entry = __ pc();
  // expression stack must be empty before entering the VM if an
  // exception happened
  __ empty_expression_stack();
  // ??? convention: expect array in register A1
  __ call_VM(noreg, CAST_FROM_FN_PTR(address,
  InterpreterRuntime::throw_ArrayIndexOutOfBoundsException), A1, A2);
  return entry;
}

address TemplateInterpreterGenerator::generate_ClassCastException_handler() {
  address entry = __ pc();
  // expression stack must be empty before entering the VM if an
  // exception happened
  __ empty_expression_stack();
  __ call_VM(noreg, CAST_FROM_FN_PTR(address, InterpreterRuntime::throw_ClassCastException),  FSR);
  return entry;
}

address TemplateInterpreterGenerator::generate_exception_handler_common(
        const char* name, const char* message, bool pass_oop) {
  assert(!pass_oop || message == nullptr, "either oop or message but not both");
  address entry = __ pc();

  // expression stack must be empty before entering the VM if an exception happened
  __ empty_expression_stack();
  // setup parameters
  __ li(A1, (long)name);
  if (pass_oop) {
    __ call_VM(V0,
    CAST_FROM_FN_PTR(address, InterpreterRuntime::create_klass_exception), A1, FSR);
  } else {
    __ li(A2, (long)message);
    __ call_VM(V0,
    CAST_FROM_FN_PTR(address, InterpreterRuntime::create_exception), A1, A2);
  }
  // throw exception
  __ jmp(Interpreter::throw_exception_entry(), relocInfo::none);
  return entry;
}

address TemplateInterpreterGenerator::generate_return_entry_for(TosState state, int step, size_t index_size) {

  address entry = __ pc();

  // Restore stack bottom in case i2c adjusted stack
  __ ld_d(AT, Address(FP, frame::interpreter_frame_last_sp_offset * wordSize));
  __ alsl_d(SP, AT, FP, LogBytesPerWord-1);
  // and null it as marker that sp is now tos until next java call
  __ st_d(R0, FP, frame::interpreter_frame_last_sp_offset * wordSize);

  __ restore_bcp();
  __ restore_locals();

  // mdp: T8
  // ret: FSR
  // tmp: T4
  if (state == atos) {
    Register mdp = T8;
    Register tmp = T4;
    __ profile_return_type(mdp, FSR, tmp);
  }


  const Register cache = T4;
  const Register index = T3;
  if (index_size == sizeof(u4)) {
    __ load_resolved_indy_entry(cache, index);
    __ ld_hu(cache, Address(cache, in_bytes(ResolvedIndyEntry::num_parameters_offset())));
    __ alsl_d(SP, cache, SP, Interpreter::logStackElementSize - 1);
  } else {
    assert(index_size == sizeof(u2), "Can only be u2");
    __ load_method_entry(cache, index);
    __ ld_hu(cache, Address(cache, in_bytes(ResolvedMethodEntry::num_parameters_offset())));
    __ alsl_d(SP, cache, SP, Interpreter::logStackElementSize - 1);
  }

  __ check_and_handle_popframe(TREG);
  __ check_and_handle_earlyret(TREG);

  __ get_dispatch();
  __ dispatch_next(state, step);

  return entry;
}


address TemplateInterpreterGenerator::generate_deopt_entry_for(TosState state,
                                                               int step,
                                                               address continuation) {
  address entry = __ pc();
  __ restore_bcp();
  __ restore_locals();
  __ get_dispatch();

  // null last_sp until next java call
  __ st_d(R0, FP, frame::interpreter_frame_last_sp_offset * wordSize);

#if INCLUDE_JVMCI
  // Check if we need to take lock at entry of synchronized method.  This can
  // only occur on method entry so emit it only for vtos with step 0.
  if (EnableJVMCI && state == vtos && step == 0) {
    Label L;
    __ ld_b(AT, Address(TREG, JavaThread::pending_monitorenter_offset()));
    __ beqz(AT, L);
    // Clear flag.
    __ st_b(R0, Address(TREG, JavaThread::pending_monitorenter_offset()));
    // Take lock.
    lock_method();
    __ bind(L);
  } else {
#ifdef ASSERT
    if (EnableJVMCI) {
      Label L;
      __ ld_b(AT, Address(TREG, JavaThread::pending_monitorenter_offset()));
      __ beqz(AT, L);
      __ stop("unexpected pending monitor in deopt entry");
      __ bind(L);
    }
#endif
  }
#endif

  // handle exceptions
  {
    Label L;
    __ ld_d(AT, TREG, in_bytes(Thread::pending_exception_offset()));
    __ beq(AT, R0, L);
    __ call_VM(noreg, CAST_FROM_FN_PTR(address, InterpreterRuntime::throw_pending_exception));
    __ should_not_reach_here();
    __ bind(L);
  }
  if (continuation == nullptr) {
    __ dispatch_next(state, step);
  } else {
    __ jump_to_entry(continuation);
  }
  return entry;
}

address TemplateInterpreterGenerator::generate_result_handler_for(BasicType type) {
  address entry = __ pc();
  if (type == T_OBJECT) {
    // retrieve result from frame
    __ ld_d(V0, FP, frame::interpreter_frame_oop_temp_offset * wordSize);
    // and verify it
    __ verify_oop(V0);
  } else {
    __ cast_primitive_type(type, V0);
  }

  __ jr(RA); // return from result handler
  return entry;
}

address TemplateInterpreterGenerator::generate_safept_entry_for(
        TosState state,
        address runtime_entry) {
  address entry = __ pc();
  __ push(state);
  __ push_cont_fastpath(TREG);
  __ call_VM(noreg, runtime_entry);
  __ pop_cont_fastpath(TREG);
  __ dispatch_via(vtos, Interpreter::_normal_table.table_for(vtos));
  return entry;
}

address TemplateInterpreterGenerator::generate_cont_resume_interpreter_adapter() {
  if (!Continuations::enabled()) return nullptr;
  address start = __ pc();

  __ restore_bcp();
  __ restore_locals();

  // Restore the last_sp and null it out
  __ ld_d(AT, FP, frame::interpreter_frame_last_sp_offset * wordSize);
  __ alsl_d(SP, AT, FP, LogBytesPerWord-1);
  __ st_d(R0, FP, frame::interpreter_frame_last_sp_offset * wordSize);

  // Restore method
  __ ld_d(Rmethod, Address(FP, frame::interpreter_frame_method_offset * wordSize));

  // Restore dispatch
  __ get_dispatch();

  __ jr(RA);

  return start;
}


// Helpers for commoning out cases in the various type of method entries.
//


// increment invocation count & check for overflow
//
// Note: checking for negative value instead of overflow
//       so we have a 'sticky' overflow test
//
// Rmethod: method
void TemplateInterpreterGenerator::generate_counter_incr(Label* overflow) {
  Label done;
  int increment = InvocationCounter::count_increment;
  Label no_mdo;
  if (ProfileInterpreter) {
    // Are we profiling?
    __ ld_d(T0, Address(Rmethod, Method::method_data_offset()));
    __ beq(T0, R0, no_mdo);
    // Increment counter in the MDO
    const Address mdo_invocation_counter(T0, in_bytes(MethodData::invocation_counter_offset()) +
                                              in_bytes(InvocationCounter::counter_offset()));
    const Address mask(T0, in_bytes(MethodData::invoke_mask_offset()));
    __ increment_mask_and_jump(mdo_invocation_counter, increment, mask, T1, false, Assembler::zero, overflow);
    __ b(done);
  }
  __ bind(no_mdo);
  // Increment counter in MethodCounters
  const Address invocation_counter(T0,
                MethodCounters::invocation_counter_offset() +
                InvocationCounter::counter_offset());
  __ get_method_counters(Rmethod, T0, done);
  const Address mask(T0, in_bytes(MethodCounters::invoke_mask_offset()));
  __ increment_mask_and_jump(invocation_counter, increment, mask, T1, false, Assembler::zero, overflow);
  __ bind(done);
}

void TemplateInterpreterGenerator::generate_counter_overflow(Label& do_continue) {

  // Asm interpreter on entry
  // S7 - locals
  // S0 - bcp
  // Rmethod - method
  // FP - interpreter frame

  // On return (i.e. jump to entry_point)
  // Rmethod - method
  // RA - return address of interpreter caller
  // tos - the last parameter to Java method
  // SP - sender_sp

  // the bcp is valid if and only if it's not null
  __ call_VM(NOREG, CAST_FROM_FN_PTR(address,
      InterpreterRuntime::frequency_counter_overflow), R0);
  __ ld_d(Rmethod, FP, method_offset);
  // Preserve invariant that S0/S7 contain bcp/locals of sender frame
  __ b_far(do_continue);
}

// See if we've got enough room on the stack for locals plus overhead.
// The expression stack grows down incrementally, so the normal guard
// page mechanism will work for that.
//
// NOTE: Since the additional locals are also always pushed (wasn't
// obvious in generate_method_entry) so the guard should work for them
// too.
//
// Args:
//      T2: number of additional locals this frame needs (what we must check)
//      T0: Method*
//
void TemplateInterpreterGenerator::generate_stack_overflow_check(void) {
  // see if we've got enough room on the stack for locals plus overhead.
  // the expression stack grows down incrementally, so the normal guard
  // page mechanism will work for that.
  //
  // Registers live on entry:
  //
  // T0: Method*
  // T2: number of additional locals this frame needs (what we must check)

  // NOTE:  since the additional locals are also always pushed (wasn't obvious in
  // generate_method_entry) so the guard should work for them too.
  //

  const int entry_size = frame::interpreter_frame_monitor_size_in_bytes();

  // total overhead size: entry_size + (saved fp thru expr stack bottom).
  // be sure to change this if you add/subtract anything to/from the overhead area
  const int overhead_size = -(frame::interpreter_frame_initial_sp_offset*wordSize)
    + entry_size;

  const size_t page_size = os::vm_page_size();
  Label after_frame_check;

  // see if the frame is greater than one page in size. If so,
  // then we need to verify there is enough stack space remaining
  // for the additional locals.
  __ li(AT, (page_size - overhead_size) / Interpreter::stackElementSize);
  __ bge(AT, T2, after_frame_check);

  // compute sp as if this were going to be the last frame on
  // the stack before the red zone

  // locals + overhead, in bytes
  __ slli_d(T3, T2, Interpreter::logStackElementSize);
  __ addi_d(T3, T3, overhead_size);   // locals * 4 + overhead_size --> T3

#ifdef ASSERT
  Label stack_base_okay, stack_size_okay;
  // verify that thread stack base is non-zero
  __ ld_d(AT, TREG, in_bytes(Thread::stack_base_offset()));
  __ bne(AT, R0, stack_base_okay);
  __ stop("stack base is zero");
  __ bind(stack_base_okay);
  // verify that thread stack size is non-zero
  __ ld_d(AT, TREG, in_bytes(Thread::stack_size_offset()));
  __ bne(AT, R0, stack_size_okay);
  __ stop("stack size is zero");
  __ bind(stack_size_okay);
#endif

  // Add stack base to locals and subtract stack size
  __ ld_d(AT, TREG, in_bytes(Thread::stack_base_offset())); // stack_base --> AT
  __ add_d(T3, T3, AT);   // locals * 4 + overhead_size + stack_base--> T3
  __ ld_d(AT, TREG, in_bytes(Thread::stack_size_offset()));  // stack_size --> AT
  __ sub_d(T3, T3, AT);  // locals * 4 + overhead_size + stack_base - stack_size --> T3

  // Use the bigger size for banging.
  const int max_bang_size = (int)MAX2(StackOverflow::stack_shadow_zone_size(), StackOverflow::stack_guard_zone_size());

  // add in the redzone and yellow size
  __ li(AT, max_bang_size);
  __ add_d(T3, T3, AT);

  // check against the current stack bottom
  __ blt(T3, SP, after_frame_check);

  // Note: the restored frame is not necessarily interpreted.
  // Use the shared runtime version of the StackOverflowError.
  __ move(SP, Rsender);
  assert(SharedRuntime::throw_StackOverflowError_entry() != nullptr, "stub not yet generated");
  __ jmp(SharedRuntime::throw_StackOverflowError_entry(), relocInfo::runtime_call_type);

  // all done with frame size check
  __ bind(after_frame_check);
}

// Allocate monitor and lock method (asm interpreter)
// Rmethod - Method*
void TemplateInterpreterGenerator::lock_method(void) {
  // synchronize method
  const int entry_size = frame::interpreter_frame_monitor_size_in_bytes();

#ifdef ASSERT
  { Label L;
    __ ld_w(T0, Rmethod, in_bytes(Method::access_flags_offset()));
    __ test_bit(T0, T0, exact_log2(JVM_ACC_SYNCHRONIZED));
    __ bne(T0, R0, L);
    __ stop("method doesn't need synchronization");
    __ bind(L);
  }
#endif // ASSERT
  // get synchronization object
  {
    Label done;
    __ ld_w(T0, Rmethod, in_bytes(Method::access_flags_offset()));
    __ test_bit(T2, T0, exact_log2(JVM_ACC_STATIC));
    __ ld_d(T0, LVP, Interpreter::local_offset_in_bytes(0));
    __ beq(T2, R0, done);
    __ load_mirror(T0, Rmethod, SCR2, SCR1);
    __ bind(done);
  }
  // add space for monitor & lock
  __ addi_d(SP, SP, (-1) * entry_size);           // add space for a monitor entry
  __ sub_d(AT, SP, FP);
  __ srai_d(AT, AT, Interpreter::logStackElementSize);
  __ st_d(AT, FP, frame::interpreter_frame_monitor_block_top_offset * wordSize);
  // set new monitor block top
  __ st_d(T0, Address(SP, BasicObjectLock::obj_offset()));   // store object

  const Register lock_reg = T0;
  __ move(lock_reg, SP);      // object address
  __ lock_object(lock_reg);
}

// Generate a fixed interpreter frame. This is identical setup for
// interpreted methods and for native methods hence the shared code.
void TemplateInterpreterGenerator::generate_fixed_frame(bool native_call) {

  // [ local var m-1      ] <--- sp
  //   ...
  // [ local var 0        ]
  // [ argument word n-1  ] <--- T0(sender's sp)
  //   ...
  // [ argument word 0    ] <--- S7

  // initialize fixed part of activation frame
  // sender's sp in Rsender
  int i = 2;
  int frame_size = 11;

  __ addi_d(SP, SP, (-frame_size) * wordSize);
  __ st_d(RA, SP, (frame_size - 1) * wordSize);   // save return address
  __ st_d(FP, SP, (frame_size - 2) * wordSize);  // save sender's fp
  __ addi_d(FP, SP, (frame_size) * wordSize);
  __ st_d(Rsender, FP, (-++i) * wordSize);  // save sender's sp
  __ st_d(R0, FP,(-++i) * wordSize);       //save last_sp as null
  __ sub_d(AT, LVP, FP);
  __ srli_d(AT, AT, Interpreter::logStackElementSize);
  // Store relativized LVP, see frame::interpreter_frame_locals().
  __ st_d(AT, FP, (-++i) * wordSize);  // save locals offset
  __ ld_d(BCP, Rmethod, in_bytes(Method::const_offset())); // get constMethodOop
  __ addi_d(BCP, BCP, in_bytes(ConstMethod::codes_offset())); // get codebase
  __ st_d(Rmethod, FP, (-++i) * wordSize);                              // save Method*
  // Get mirror and store it in the frame as GC root for this Method*
  __ load_mirror(T2, Rmethod, SCR2, SCR1);
  __ st_d(T2, FP, (-++i) * wordSize); // Mirror

  if (ProfileInterpreter) {
    Label method_data_continue;
    __ ld_d(AT, Rmethod,  in_bytes(Method::method_data_offset()));
    __ beq(AT, R0, method_data_continue);
    __ addi_d(AT, AT, in_bytes(MethodData::data_offset()));
    __ bind(method_data_continue);
    __ st_d(AT, FP,  (-++i) * wordSize);
  } else {
    __ st_d(R0, FP, (-++i) * wordSize);
  }

  __ ld_d(T2, Rmethod, in_bytes(Method::const_offset()));
  __ ld_d(T2, T2, in_bytes(ConstMethod::constants_offset()));
  __ ld_d(T2, Address(T2, ConstantPool::cache_offset()));
  __ st_d(T2, FP, (-++i) * wordSize);                    // set constant pool cache
  if (native_call) {
    __ st_d(R0, FP, (-++i) * wordSize);          // no bcp
  } else {
    __ st_d(BCP, FP, (-++i) * wordSize);          // set bcp
  }
  __ li(AT, frame::interpreter_frame_initial_sp_offset);
  __ st_d(AT, FP, (-++i) * wordSize);               // reserve word for pointer to expression stack bottom
  assert(i == frame_size, "i should be equal to frame_size");
}

// End of helpers

// Various method entries
//------------------------------------------------------------------------------------------------------------------------
//
//

// Method entry for java.lang.ref.Reference.get.
address TemplateInterpreterGenerator::generate_Reference_get_entry(void) {
  // Code: _aload_0, _getfield, _areturn
  // parameter size = 1
  //
  // The code that gets generated by this routine is split into 2 parts:
  //    1. The "intrinsified" code for G1 (or any SATB based GC),
  //    2. The slow path - which is an expansion of the regular method entry.
  //
  // Notes:-
  // * In the G1 code we do not check whether we need to block for
  //   a safepoint. If G1 is enabled then we must execute the specialized
  //   code for Reference.get (except when the Reference object is null)
  //   so that we can log the value in the referent field with an SATB
  //   update buffer.
  //   If the code for the getfield template is modified so that the
  //   G1 pre-barrier code is executed when the current method is
  //   Reference.get() then going through the normal method entry
  //   will be fine.
  // * The G1 code can, however, check the receiver object (the instance
  //   of java.lang.Reference) and jump to the slow path if null. If the
  //   Reference object is null then we obviously cannot fetch the referent
  //   and so we don't need to call the G1 pre-barrier. Thus we can use the
  //   regular method entry code to generate the NPE.
  //
  // This code is based on generate_accessor_entry.
  //
  // Rmethod: Method*
  // Rsender: senderSP must preserve for slow path, set SP to it on fast path
  // RA is live. It must be saved around calls.

  address entry = __ pc();

  const int referent_offset = java_lang_ref_Reference::referent_offset();

  Label slow_path;
  const Register local_0 = A0;
  // Check if local 0 != nullptr
  // If the receiver is null then it is OK to jump to the slow path.
  __ ld_d(local_0, Address(SP, 0));
  __ beqz(local_0, slow_path);

  // Load the value of the referent field.
  const Address field_address(local_0, referent_offset);
  BarrierSetAssembler *bs = BarrierSet::barrier_set()->barrier_set_assembler();
  bs->load_at(_masm, IN_HEAP | ON_WEAK_OOP_REF, T_OBJECT, local_0, field_address, /*tmp1*/ SCR2, /*tmp2*/ SCR1);

  // areturn
  __ move(SP, Rsender);
  __ jr(RA);

  // generate a vanilla interpreter entry as the slow path
  __ bind(slow_path);
  __ jump_to_entry(Interpreter::entry_for_kind(Interpreter::zerolocals));
  return entry;
}

// Interpreter stub for calling a native method. (asm interpreter)
// This sets up a somewhat different looking stack for calling the
// native method than the typical interpreter frame setup.
address TemplateInterpreterGenerator::generate_native_entry(bool synchronized) {
  // determine code generation flags
  bool inc_counter  = UseCompiler || CountCompiledCalls;
  // Rsender: sender's sp
  // Rmethod: Method*
  address entry_point = __ pc();

  // get parameter size (always needed)
  // the size in the java stack
  __ ld_d(V0, Rmethod, in_bytes(Method::const_offset()));
  __ ld_hu(V0, V0, in_bytes(ConstMethod::size_of_parameters_offset()));

  // native calls don't need the stack size check since they have no expression stack
  // and the arguments are already on the stack and we only add a handful of words
  // to the stack

  // Rmethod: Method*
  // V0: size of parameters
  // Layout of frame at this point
  //
  // [ argument word n-1  ] <--- sp
  //   ...
  // [ argument word 0    ]

  // for natives the size of locals is zero

  // compute beginning of parameters (S7)
  __ slli_d(LVP, V0, Address::times_8);
  __ addi_d(LVP, LVP, (-1) * wordSize);
  __ add_d(LVP, LVP, SP);


  // add 2 zero-initialized slots for native calls
  // 1 slot for native oop temp offset (setup via runtime)
  // 1 slot for static native result handler3 (setup via runtime)
  __ push2(R0, R0);

  // Layout of frame at this point
  // [ method holder mirror  ] <--- sp
  // [ result type info      ]
  // [ argument word n-1     ] <--- T0
  //   ...
  // [ argument word 0       ] <--- LVP

  // initialize fixed part of activation frame
  generate_fixed_frame(true);
  // after this function, the layout of frame is as following
  //
  // [ monitor block top        ] <--- sp ( the top monitor entry )
  // [ byte code pointer (0)    ] (if native, bcp = 0)
  // [ constant pool cache      ]
  // [ Mirror                   ]
  // [ Method*                  ]
  // [ locals offset            ]
  // [ sender's sp              ]
  // [ sender's fp              ]
  // [ return address           ] <--- fp
  // [ method holder mirror     ]
  // [ result type info         ]
  // [ argument word n-1        ] <--- sender's sp
  //   ...
  // [ argument word 0          ] <--- S7


  // make sure method is native & not abstract
#ifdef ASSERT
  __ ld_w(T0, Rmethod, in_bytes(Method::access_flags_offset()));
  {
    Label L;
    __ test_bit(AT, T0, exact_log2(JVM_ACC_NATIVE));
    __ bne(AT, R0, L);
    __ stop("tried to execute native method as non-native");
    __ bind(L);
  }
  {
    Label L;
    __ test_bit(AT, T0, exact_log2(JVM_ACC_ABSTRACT));
    __ beq(AT, R0, L);
    __ stop("tried to execute abstract method in interpreter");
    __ bind(L);
  }
#endif

  // Since at this point in the method invocation the exception handler
  // would try to exit the monitor of synchronized methods which hasn't
  // been entered yet, we set the thread local variable
  // _do_not_unlock_if_synchronized to true. The remove_activation will
  // check this flag.

  __ li(AT, (int)true);
  __ st_b(AT, TREG, in_bytes(JavaThread::do_not_unlock_if_synchronized_offset()));

  // increment invocation count & check for overflow
  Label invocation_counter_overflow;
  if (inc_counter) {
    generate_counter_incr(&invocation_counter_overflow);
  }

  Label continue_after_compile;
  __ bind(continue_after_compile);

  bang_stack_shadow_pages(true);

  // reset the _do_not_unlock_if_synchronized flag
  __ st_b(R0, TREG, in_bytes(JavaThread::do_not_unlock_if_synchronized_offset()));

  // check for synchronized methods
  // Must happen AFTER invocation_counter check and stack overflow check,
  // so method is not locked if overflows.
  if (synchronized) {
    lock_method();
  } else {
    // no synchronization necessary
#ifdef ASSERT
    {
      Label L;
      __ ld_w(T0, Rmethod, in_bytes(Method::access_flags_offset()));
      __ test_bit(AT, T0, exact_log2(JVM_ACC_SYNCHRONIZED));
      __ beq(AT, R0, L);
      __ stop("method needs synchronization");
      __ bind(L);
    }
#endif
  }

  // after method_lock, the layout of frame is as following
  //
  // [ monitor entry            ] <--- sp
  //   ...
  // [ monitor entry            ]
  // [ monitor block top        ] ( the top monitor entry )
  // [ byte code pointer (0)    ] (if native, bcp = 0)
  // [ constant pool cache      ]
  // [ Mirror                   ]
  // [ Method*                  ]
  // [ locals offset            ]
  // [ sender's sp              ]
  // [ sender's fp              ]
  // [ return address           ] <--- fp
  // [ method holder mirror     ]
  // [ result type info         ]
  // [ argument word n-1        ] <--- ( sender's sp )
  //   ...
  // [ argument word 0          ] <--- S7

  // start execution
#ifdef ASSERT
  {
    Label L;
    __ ld_d(AT, FP, frame::interpreter_frame_monitor_block_top_offset * wordSize);
    __ alsl_d(AT, AT, FP, LogBytesPerWord-1);
    __ beq(AT, SP, L);
    __ stop("broken stack frame setup in interpreter in asm");
    __ bind(L);
  }
#endif

  // jvmti/jvmpi support
  __ notify_method_entry();

  // work registers
  const Register method = Rmethod;
  const Register t      = T8;

  __ get_method(method);
  {
    Label L, Lstatic;
    __ ld_d(t,method,in_bytes(Method::const_offset()));
    __ ld_hu(t, t, in_bytes(ConstMethod::size_of_parameters_offset()));
    // LoongArch ABI: caller does not reserve space for the register auguments.
    // A0 and A1(if needed)
    __ ld_w(AT, Rmethod, in_bytes(Method::access_flags_offset()));
    __ test_bit(AT, AT, exact_log2(JVM_ACC_STATIC));
    __ beq(AT, R0, Lstatic);
    __ addi_d(t, t, 1);
    __ bind(Lstatic);
    __ addi_d(t, t, -7);
    __ bge(R0, t, L);
    __ slli_d(t, t, Address::times_8);
    __ sub_d(SP, SP, t);
    __ bind(L);
  }
  assert(StackAlignmentInBytes == 16, "must be");
  __ bstrins_d(SP, R0, 3, 0);
  __ move(AT, SP);
  // [                          ] <--- sp
  //   ...                        (size of parameters - 8 )
  // [ monitor entry            ]
  //   ...
  // [ monitor entry            ]
  // [ monitor block top        ] ( the top monitor entry )
  // [ byte code pointer (0)    ] (if native, bcp = 0)
  // [ constant pool cache      ]
  // [ Mirror                   ]
  // [ Method*                  ]
  // [ locals offset            ]
  // [ sender's sp              ]
  // [ sender's fp              ]
  // [ return address           ] <--- fp
  // [ method holder mirror     ]
  // [ result type info         ]
  // [ argument word n-1        ] <--- ( sender's sp )
  //   ...
  // [ argument word 0          ] <--- LVP

  // get signature handler
  {
    Label L;
    __ ld_d(T4, method, in_bytes(Method::signature_handler_offset()));
    __ bne(T4, R0, L);
    __ call_VM(NOREG, CAST_FROM_FN_PTR(address,
               InterpreterRuntime::prepare_native_call), method);
    __ get_method(method);
    __ ld_d(T4, method, in_bytes(Method::signature_handler_offset()));
    __ bind(L);
  }

  // call signature handler
  // FIXME: when change codes in InterpreterRuntime, note this point
  // from: begin of parameters
  assert(InterpreterRuntime::SignatureHandlerGenerator::from() == LVP, "adjust this code");
  // to: current sp
  assert(InterpreterRuntime::SignatureHandlerGenerator::to  () == SP, "adjust this code");
  // temp: T3
  assert(InterpreterRuntime::SignatureHandlerGenerator::temp() == t  , "adjust this code");

  __ jalr(T4);
  __ get_method(method);

  //
  // if native function is static, and its second parameter has type length of double word,
  // and first parameter has type length of word, we have to reserve one word
  // for the first parameter, according to LoongArch abi.
  // if native function is not static, and its third parameter has type length of double word,
  // and second parameter has type length of word, we have to reserve one word for the second
  // parameter.
  //


  // result handler is in V0
  // set result handler
  __ st_d(V0, FP, (frame::interpreter_frame_result_handler_offset)*wordSize);

#define FIRSTPARA_SHIFT_COUNT 5
#define SECONDPARA_SHIFT_COUNT 9
#define THIRDPARA_SHIFT_COUNT 13
#define PARA_MASK  0xf

  // pass mirror handle if static call
  {
    Label L;
    __ ld_w(t, method, in_bytes(Method::access_flags_offset()));
    __ test_bit(AT, t, exact_log2(JVM_ACC_STATIC));
    __ beq(AT, R0, L);

    // get mirror
    __ load_mirror(t, method, SCR2, SCR1);
    // copy mirror into activation frame
    __ st_d(t, FP, frame::interpreter_frame_oop_temp_offset * wordSize);
    // pass handle to mirror
    __ addi_d(t, FP, frame::interpreter_frame_oop_temp_offset * wordSize);
    __ move(A1, t);
    __ bind(L);
  }

  // [ mthd holder mirror ptr   ] <--- sp  --------------------| (only for static method)
  // [                          ]                              |
  //   ...                        size of parameters(or +1)    |
  // [ monitor entry            ]                              |
  //   ...                                                     |
  // [ monitor entry            ]                              |
  // [ monitor block top        ] ( the top monitor entry )    |
  // [ byte code pointer (0)    ] (if native, bcp = 0)         |
  // [ constant pool cache      ]                              |
  // [ Mirror                   ]                              |
  // [ Method*                  ]                              |
  // [ locals offset            ]                              |
  // [ sender's sp              ]                              |
  // [ sender's fp              ]                              |
  // [ return address           ] <--- fp                      |
  // [ method holder mirror     ] <----------------------------|
  // [ result type info         ]
  // [ argument word n-1        ] <--- ( sender's sp )
  //   ...
  // [ argument word 0          ] <--- S7

  // get native function entry point
  { Label L;
    __ ld_d(T4, method, in_bytes(Method::native_function_offset()));
    __ li(T6, SharedRuntime::native_method_throw_unsatisfied_link_error_entry());
    __ bne(T6, T4, L);
    __ call_VM(noreg, CAST_FROM_FN_PTR(address, InterpreterRuntime::prepare_native_call), method);
    __ get_method(method);
    __ ld_d(T4, method, in_bytes(Method::native_function_offset()));
    __ bind(L);
  }

  // pass JNIEnv
  __ addi_d(A0, TREG, in_bytes(JavaThread::jni_environment_offset()));
  // [ jni environment          ] <--- sp
  // [ mthd holder mirror ptr   ] ---------------------------->| (only for static method)
  // [                          ]                              |
  //   ...                        size of parameters           |
  // [ monitor entry            ]                              |
  //   ...                                                     |
  // [ monitor entry            ]                              |
  // [ monitor block top        ] ( the top monitor entry )    |
  // [ byte code pointer (0)    ] (if native, bcp = 0)         |
  // [ constant pool cache      ]                              |
  // [ Mirror                   ]                              |
  // [ Method*                  ]                              |
  // [ locals offset            ]                              |
  // [ sender's sp              ]                              |
  // [ sender's fp              ]                              |
  // [ return address           ] <--- fp                      |
  // [ method holder mirror     ] <----------------------------|
  // [ result type info         ]
  // [ argument word n-1        ] <--- ( sender's sp )
  //   ...
  // [ argument word 0          ] <--- S7

  // Set the last Java PC in the frame anchor to be the return address from
  // the call to the native method: this will allow the debugger to
  // generate an accurate stack trace.
  Label native_return;
  __ set_last_Java_frame(TREG, SP, FP, native_return);

  // change thread state
#ifdef ASSERT
  {
    Label L;
    __ ld_w(t, TREG, in_bytes(JavaThread::thread_state_offset()));
    __ addi_d(t, t, (-1) * _thread_in_Java);
    __ beq(t, R0, L);
    __ stop("Wrong thread state in native stub");
    __ bind(L);
  }
#endif

  __ li(t, _thread_in_native);
  if (os::is_MP()) {
    __ addi_d(AT, TREG, in_bytes(JavaThread::thread_state_offset()));
    __ amswap_db_w(R0, t, AT);
  } else {
    __ st_w(t, TREG, in_bytes(JavaThread::thread_state_offset()));
  }

  __ push_cont_fastpath();

  // call native method
  __ jalr(T4);

  __ pop_cont_fastpath();

  // result potentially in V0 or F0


  // via _last_native_pc and not via _last_jave_sp
  // NOTE: the order of these push(es) is known to frame::interpreter_frame_result.
  //  If the order changes or anything else is added to the stack the code in
  // interpreter_frame_result will have to be changed.
  //FIXME, should modify here
  // save return value to keep the value from being destroyed by other calls
  __ push(dtos);
  __ push(ltos);

  // change thread state
  __ li(t, _thread_in_native_trans);
  if (os::is_MP()) {
    __ addi_d(AT, TREG, in_bytes(JavaThread::thread_state_offset()));
    __ amswap_db_w(R0, t, AT); // Release-Store

    // Force this write out before the read below
    if (!UseSystemMemoryBarrier) {
      __ membar(__ AnyAny);
    }
  } else {
    __ st_w(t, TREG, in_bytes(JavaThread::thread_state_offset()));
  }

  // check for safepoint operation in progress and/or pending suspend requests
  { Label Continue;

    // Don't use call_VM as it will see a possible pending exception and forward it
    // and never return here preventing us from clearing _last_native_pc down below.
    // Also can't use call_VM_leaf either as it will check to see if BCP & LVP are
    // preserved and correspond to the bcp/locals pointers. So we do a runtime call
    // by hand.
    //
    Label slow_path;

    // We need an acquire here to ensure that any subsequent load of the
    // global SafepointSynchronize::_state flag is ordered after this load
    // of the thread-local polling word.  We don't want this poll to
    // return false (i.e. not safepointing) and a later poll of the global
    // SafepointSynchronize::_state spuriously to return true.
    //
    // This is to avoid a race when we're in a native->Java transition
    // racing the code which wakes up from a safepoint.
    __ safepoint_poll(slow_path, TREG, true /* at_return */, true /* acquire */, false /* in_nmethod */);
    __ ld_w(AT, TREG, in_bytes(JavaThread::suspend_flags_offset()));
    __ beq(AT, R0, Continue);
    __ bind(slow_path);
    __ move(A0, TREG);
    __ call(CAST_FROM_FN_PTR(address, JavaThread::check_special_condition_for_native_trans),
                             relocInfo::runtime_call_type);

    //add for compressedoops
    __ reinit_heapbase();
    __ bind(Continue);
  }

  // change thread state
  __ li(t, _thread_in_Java);
  if (os::is_MP()) {
    __ addi_d(AT, TREG, in_bytes(JavaThread::thread_state_offset()));
    __ amswap_db_w(R0, t, AT);
  } else {
    __ st_w(t, TREG, in_bytes(JavaThread::thread_state_offset()));
  }

  if (LockingMode != LM_LEGACY) {
    // Check preemption for Object.wait()
    Label not_preempted;
    __ ld_d(AT, Address(TREG, JavaThread::preempt_alternate_return_offset()));
    __ beqz(AT, not_preempted);
    __ st_d(R0, Address(TREG, JavaThread::preempt_alternate_return_offset()));
    __ jr(AT);
    __ bind(native_return);
    __ restore_after_resume(true /* is_native */);
    __ bind(not_preempted);
  } else {
    // any pc will do so just use this one for LM_LEGACY to keep code together.
    __ bind(native_return);
  }

  __ reset_last_Java_frame(TREG, true);

  if (CheckJNICalls) {
    // clear_pending_jni_exception_check
    __ st_d(R0, TREG, in_bytes(JavaThread::pending_jni_exception_check_fn_offset()));
  }

  // reset handle block
  __ ld_d(t, TREG, in_bytes(JavaThread::active_handles_offset()));
  __ st_w(R0, Address(t, JNIHandleBlock::top_offset()));

  // If result was an oop then unbox and save it in the frame
  {
    Label no_oop;
    __ ld_d(AT, FP, frame::interpreter_frame_result_handler_offset*wordSize);
    __ li(T0, AbstractInterpreter::result_handler(T_OBJECT));
    __ bne(AT, T0, no_oop);
    __ pop(ltos);
    // Unbox oop result, e.g. JNIHandles::resolve value.
    __ resolve_jobject(V0, SCR2, SCR1);
    __ st_d(V0, FP, (frame::interpreter_frame_oop_temp_offset)*wordSize);
    // keep stack depth as expected by pushing oop which will eventually be discarded
    __ push(ltos);
    __ bind(no_oop);
  }
  {
    Label no_reguard;
    __ ld_w(t, TREG, in_bytes(JavaThread::stack_guard_state_offset()));
    __ li(AT, (u1)StackOverflow::stack_guard_yellow_reserved_disabled);
    __ bne(t, AT, no_reguard);
    __ push_call_clobbered_registers();
    __ move(S5_heapbase, SP);
    assert(StackAlignmentInBytes == 16, "must be");
    __ bstrins_d(SP, R0, 3, 0);
    __ call(CAST_FROM_FN_PTR(address, SharedRuntime::reguard_yellow_pages), relocInfo::runtime_call_type);
    __ move(SP, S5_heapbase);
    __ pop_call_clobbered_registers();
    //add for compressedoops
    __ reinit_heapbase();
    __ bind(no_reguard);
  }
  // restore BCP to have legal interpreter frame,
  // i.e., bci == 0 <=> BCP == code_base()
  // Can't call_VM until bcp is within reasonable.
  __ get_method(method);      // method is junk from thread_in_native to now.
  __ ld_d(BCP, method, in_bytes(Method::const_offset()));
  __ lea(BCP, Address(BCP, in_bytes(ConstMethod::codes_offset())));
  // handle exceptions (exception handling will handle unlocking!)
  {
    Label L;
    __ ld_d(t, TREG, in_bytes(Thread::pending_exception_offset()));
    __ beq(t, R0, L);
    // Note: At some point we may want to unify this with the code used in
    // call_VM_base();
    // i.e., we should use the StubRoutines::forward_exception code. For now this
    // doesn't work here because the sp is not correctly set at this point.
    __ MacroAssembler::call_VM(noreg,
                               CAST_FROM_FN_PTR(address,
                               InterpreterRuntime::throw_pending_exception));
    __ should_not_reach_here();
    __ bind(L);
  }

  // do unlocking if necessary
  {
    const Register monitor_reg = T0;
    Label L;
    __ ld_w(t, method, in_bytes(Method::access_flags_offset()));
    __ test_bit(t, t, exact_log2(JVM_ACC_SYNCHRONIZED));
    __ addi_d(monitor_reg, FP, frame::interpreter_frame_initial_sp_offset * wordSize - (int)sizeof(BasicObjectLock));
    __ beq(t, R0, L);
    // the code below should be shared with interpreter macro assembler implementation
    {
      Label unlock;
      // BasicObjectLock will be first in list,
      // since this is a synchronized method. However, need
      // to check that the object has not been unlocked by
      // an explicit monitorexit bytecode.
      // address of first monitor

      __ ld_d(t, Address(monitor_reg, BasicObjectLock::obj_offset()));
      __ bne(t, R0, unlock);

      // Entry already unlocked, need to throw exception
      __ MacroAssembler::call_VM(NOREG, CAST_FROM_FN_PTR(address,
      InterpreterRuntime::throw_illegal_monitor_state_exception));
      __ should_not_reach_here();

      __ bind(unlock);
      __ unlock_object(monitor_reg);
    }
    __ bind(L);
  }

  // jvmti/jvmpi support
  // Note: This must happen _after_ handling/throwing any exceptions since
  //       the exception handler code notifies the runtime of method exits
  //       too. If this happens before, method entry/exit notifications are
  //       not properly paired (was bug - gri 11/22/99).
  __ notify_method_exit(vtos, InterpreterMacroAssembler::NotifyJVMTI);

  // restore potential result in V0,
  // call result handler to restore potential result in ST0 & handle result

  __ pop(ltos);
  __ pop(dtos);

  __ ld_d(t, FP, (frame::interpreter_frame_result_handler_offset) * wordSize);
  __ jalr(t);


  // remove activation
  __ ld_d(SP, FP, frame::interpreter_frame_sender_sp_offset * wordSize); // get sender sp
  __ ld_d(RA, FP, frame::return_addr_offset * wordSize); // get return address
  __ ld_d(FP, FP, frame::link_offset * wordSize); // restore sender's fp
  __ jr(RA);

  if (inc_counter) {
    // Handle overflow of counter and compile method
    __ bind(invocation_counter_overflow);
    generate_counter_overflow(continue_after_compile);
  }

  return entry_point;
}

void TemplateInterpreterGenerator::bang_stack_shadow_pages(bool native_call) {
  // Quick & dirty stack overflow checking: bang the stack & handle trap.
  // Note that we do the banging after the frame is setup, since the exception
  // handling code expects to find a valid interpreter frame on the stack.
  // Doing the banging earlier fails if the caller frame is not an interpreter
  // frame.
  // (Also, the exception throwing code expects to unlock any synchronized
  // method receiever, so do the banging after locking the receiver.)

  // Bang each page in the shadow zone. We can't assume it's been done for
  // an interpreter frame with greater than a page of locals, so each page
  // needs to be checked.  Only true for non-native.
  const int page_size = (int)os::vm_page_size();
  const int n_shadow_pages = ((int)StackOverflow::stack_shadow_zone_size()) / page_size;
  const int start_page = native_call ? n_shadow_pages : 1;
  BLOCK_COMMENT("bang_stack_shadow_pages:");
  for (int pages = start_page; pages <= n_shadow_pages; pages++) {
    __ bang_stack_with_offset(pages*page_size);
  }
}

//
// Generic interpreted method entry to (asm) interpreter
//
// Layout of frame just at the entry
//
//   [ argument word n-1  ] <--- sp
//     ...
//   [ argument word 0    ]
// assume Method* in Rmethod before call this method.
// prerequisites to the generated stub : the callee Method* in Rmethod
// note you must save the caller bcp before call the generated stub
//
address TemplateInterpreterGenerator::generate_normal_entry(bool synchronized) {
  // determine code generation flags
  bool inc_counter  = UseCompiler || CountCompiledCalls;

  // Rmethod: Method*
  // Rsender: sender 's sp
  address entry_point = __ pc();

  const Address invocation_counter(Rmethod,
      in_bytes(MethodCounters::invocation_counter_offset() + InvocationCounter::counter_offset()));

  // get parameter size (always needed)
  __ ld_d(T3, Rmethod, in_bytes(Method::const_offset()));  //T3 --> Rmethod._constMethod
  __ ld_hu(V0, T3, in_bytes(ConstMethod::size_of_parameters_offset()));

  // Rmethod: Method*
  // V0: size of parameters
  // Rsender: sender 's sp ,could be different from sp+ wordSize if we call via c2i
  // get size of locals in words to T2
  __ ld_hu(T2, T3, in_bytes(ConstMethod::size_of_locals_offset()));
  // T2 = no. of additional locals, locals include parameters
  __ sub_d(T2, T2, V0);

  // see if we've got enough room on the stack for locals plus overhead.
  // Layout of frame at this point
  //
  // [ argument word n-1  ] <--- sp
  //   ...
  // [ argument word 0    ]
  generate_stack_overflow_check();
  // after this function, the layout of frame does not change

  // compute beginning of parameters (LVP)
  __ slli_d(LVP, V0, LogBytesPerWord);
  __ addi_d(LVP, LVP, (-1) * wordSize);
  __ add_d(LVP, LVP, SP);

  // T2 - # of additional locals
  // allocate space for locals
  // explicitly initialize locals
  {
    Label exit, loop;
    __ beq(T2, R0, exit);

    __ bind(loop);
    __ addi_d(SP, SP, (-1) * wordSize);
    __ addi_d(T2, T2, -1);               // until everything initialized
    __ st_d(R0, SP, 0);                  // initialize local variables
    __ bne(T2, R0, loop);

    __ bind(exit);
  }

  // And the base dispatch table
  __ get_dispatch();

  // initialize fixed part of activation frame
  generate_fixed_frame(false);


  // after this function, the layout of frame is as following
  //
  // [ monitor block top        ] <--- sp ( the top monitor entry )
  // [ byte code pointer        ] (if native, bcp = 0)
  // [ constant pool cache      ]
  // [ Method*                  ]
  // [ locals offset            ]
  // [ sender's sp              ]
  // [ sender's fp              ] <--- fp
  // [ return address           ]
  // [ local var m-1            ]
  //   ...
  // [ local var 0              ]
  // [ argument word n-1        ] <--- ( sender's sp )
  //   ...
  // [ argument word 0          ] <--- LVP


  // make sure method is not native & not abstract
#ifdef ASSERT
  __ ld_d(AT, Rmethod, in_bytes(Method::access_flags_offset()));
  {
    Label L;
    __ test_bit(T2, AT, exact_log2(JVM_ACC_NATIVE));
    __ beq(T2, R0, L);
    __ stop("tried to execute native method as non-native");
    __ bind(L);
  }
  {
    Label L;
    __ test_bit(T2, AT, exact_log2(JVM_ACC_ABSTRACT));
    __ beq(T2, R0, L);
    __ stop("tried to execute abstract method in interpreter");
    __ bind(L);
  }
#endif

  // Since at this point in the method invocation the exception handler
  // would try to exit the monitor of synchronized methods which hasn't
  // been entered yet, we set the thread local variable
  // _do_not_unlock_if_synchronized to true. The remove_activation will
  // check this flag.

  __ li(AT, (int)true);
  __ st_b(AT, TREG, in_bytes(JavaThread::do_not_unlock_if_synchronized_offset()));

  // mdp : T8
  // tmp1: T4
  // tmp2: T2
  __ profile_parameters_type(T8, T4, T2);

  // increment invocation count & check for overflow
  Label invocation_counter_overflow;
  if (inc_counter) {
    generate_counter_incr(&invocation_counter_overflow);
  }

  Label continue_after_compile;
  __ bind(continue_after_compile);

  bang_stack_shadow_pages(false);

  // reset the _do_not_unlock_if_synchronized flag
  __ st_b(R0, TREG, in_bytes(JavaThread::do_not_unlock_if_synchronized_offset()));

  // check for synchronized methods
  // Must happen AFTER invocation_counter check and stack overflow check,
  // so method is not locked if overflows.
  //
  if (synchronized) {
    // Allocate monitor and lock method
    lock_method();
  } else {
    // no synchronization necessary
#ifdef ASSERT
    { Label L;
      __ ld_w(AT, Rmethod, in_bytes(Method::access_flags_offset()));
      __ test_bit(AT, AT, exact_log2(JVM_ACC_SYNCHRONIZED));
      __ beqz(AT, L);
      __ stop("method needs synchronization");
      __ bind(L);
    }
#endif
  }

  // layout of frame after lock_method
  // [ monitor entry            ] <--- sp
  //   ...
  // [ monitor entry            ]
  // [ monitor block top        ] ( the top monitor entry )
  // [ byte code pointer        ] (if native, bcp = 0)
  // [ constant pool cache      ]
  // [ Method*                  ]
  // [ locals offset            ]
  // [ sender's sp              ]
  // [ sender's fp              ]
  // [ return address           ] <--- fp
  // [ local var m-1            ]
  //   ...
  // [ local var 0              ]
  // [ argument word n-1        ] <--- ( sender's sp )
  //   ...
  // [ argument word 0          ] <--- LVP


  // start execution
#ifdef ASSERT
  {
    Label L;
    __ ld_d(AT, FP, frame::interpreter_frame_monitor_block_top_offset * wordSize);
    __ alsl_d(AT, AT, FP, LogBytesPerWord-1);
    __ beq(AT, SP, L);
    __ stop("broken stack frame setup in interpreter in native");
    __ bind(L);
  }
#endif

  // jvmti/jvmpi support
  __ notify_method_entry();

  __ dispatch_next(vtos);

  // invocation counter overflow
  if (inc_counter) {
    // Handle overflow of counter and compile method
    __ bind(invocation_counter_overflow);
    generate_counter_overflow(continue_after_compile);
  }

  return entry_point;
}

//-----------------------------------------------------------------------------
// Exceptions

void TemplateInterpreterGenerator::generate_throw_exception() {
  // Entry point in previous activation (i.e., if the caller was
  // interpreted)
  Interpreter::_rethrow_exception_entry = __ pc();
  // Restore sp to interpreter_frame_last_sp even though we are going
  // to empty the expression stack for the exception processing.
  __ st_d(R0,FP, frame::interpreter_frame_last_sp_offset * wordSize);

  // V0: exception
  // V1: return address/pc that threw exception
  __ restore_bcp();                              // BCP points to call/send
  __ restore_locals();
  __ reinit_heapbase();
  __ get_dispatch();

  // Entry point for exceptions thrown within interpreter code
  Interpreter::_throw_exception_entry = __ pc();
  // expression stack is undefined here
  // V0: exception
  // BCP: exception bcp
  __ verify_oop(V0);

  // expression stack must be empty before entering the VM in case of an exception
  __ empty_expression_stack();
  // find exception handler address and preserve exception oop
  __ move(A1, V0);
  __ call_VM(V1, CAST_FROM_FN_PTR(address, InterpreterRuntime::exception_handler_for_exception), A1);
  // V0: exception handler entry point
  // V1: preserved exception oop
  // S0: bcp for exception handler
  __ push(V1);                                 // push exception which is now the only value on the stack
  __ jr(V0);                                   // jump to exception handler (may be _remove_activation_entry!)

  // If the exception is not handled in the current frame the frame is removed and
  // the exception is rethrown (i.e. exception continuation is _rethrow_exception).
  //
  // Note: At this point the bci is still the bxi for the instruction which caused
  //       the exception and the expression stack is empty. Thus, for any VM calls
  //       at this point, GC will find a legal oop map (with empty expression stack).

  // In current activation
  // V0: exception
  // BCP: exception bcp

  //
  // JVMTI PopFrame support
  //

  Interpreter::_remove_activation_preserving_args_entry = __ pc();
  __ empty_expression_stack();
  // Set the popframe_processing bit in pending_popframe_condition indicating that we are
  // currently handling popframe, so that call_VMs that may happen later do not trigger new
  // popframe handling cycles.
  __ ld_w(T3, TREG, in_bytes(JavaThread::popframe_condition_offset()));
  __ ori(T3, T3, JavaThread::popframe_processing_bit);
  __ st_w(T3, TREG, in_bytes(JavaThread::popframe_condition_offset()));

  {
    // Check to see whether we are returning to a deoptimized frame.
    // (The PopFrame call ensures that the caller of the popped frame is
    // either interpreted or compiled and deoptimizes it if compiled.)
    // In this case, we can't call dispatch_next() after the frame is
    // popped, but instead must save the incoming arguments and restore
    // them after deoptimization has occurred.
    //
    // Note that we don't compare the return PC against the
    // deoptimization blob's unpack entry because of the presence of
    // adapter frames in C2.
    Label caller_not_deoptimized;
    __ ld_d(A0, FP, frame::return_addr_offset * wordSize);
    __ super_call_VM_leaf(CAST_FROM_FN_PTR(address, InterpreterRuntime::interpreter_contains), A0);
    __ bne(V0, R0, caller_not_deoptimized);

    // Compute size of arguments for saving when returning to deoptimized caller
    __ get_method(A1);
    __ ld_d(A1, A1, in_bytes(Method::const_offset()));
    __ ld_hu(A1, A1, in_bytes(ConstMethod::size_of_parameters_offset()));
    __ slli_d(A1, A1, Interpreter::logStackElementSize);
    __ restore_locals();
    __ sub_d(A2, LVP, A1);
    __ addi_d(A2, A2, wordSize);
    // Save these arguments
    __ move(A0, TREG);
    __ super_call_VM_leaf(CAST_FROM_FN_PTR(address, Deoptimization::popframe_preserve_args), A0, A1, A2);

    __ remove_activation(vtos,
                         /* throw_monitor_exception */ false,
                         /* install_monitor_exception */ false,
                         /* notify_jvmdi */ false);

    // Inform deoptimization that it is responsible for restoring these arguments
    __ li(AT, JavaThread::popframe_force_deopt_reexecution_bit);
    __ st_w(AT, TREG, in_bytes(JavaThread::popframe_condition_offset()));
    // Continue in deoptimization handler
    __ jr(RA);

    __ bind(caller_not_deoptimized);
  }

  __ remove_activation(vtos,
                       /* throw_monitor_exception */ false,
                       /* install_monitor_exception */ false,
                       /* notify_jvmdi */ false);

  // Clear the popframe condition flag
  // Finish with popframe handling
  // A previous I2C followed by a deoptimization might have moved the
  // outgoing arguments further up the stack. PopFrame expects the
  // mutations to those outgoing arguments to be preserved and other
  // constraints basically require this frame to look exactly as
  // though it had previously invoked an interpreted activation with
  // no space between the top of the expression stack (current
  // last_sp) and the top of stack. Rather than force deopt to
  // maintain this kind of invariant all the time we call a small
  // fixup routine to move the mutated arguments onto the top of our
  // expression stack if necessary.
  __ move(T8, SP);
  __ ld_d(AT, FP, frame::interpreter_frame_last_sp_offset * wordSize);
  __ alsl_d(A2, AT, FP, LogBytesPerWord-1);
  // PC must point into interpreter here
  Label L;
  __ bind(L);
  __ set_last_Java_frame(TREG, noreg, FP, L);
  __ super_call_VM_leaf(CAST_FROM_FN_PTR(address, InterpreterRuntime::popframe_move_outgoing_args), TREG, T8, A2);
  __ reset_last_Java_frame(TREG, true);
  // Restore the last_sp and null it out
  __ ld_d(AT, FP, frame::interpreter_frame_last_sp_offset * wordSize);
  __ alsl_d(SP, AT, FP, LogBytesPerWord-1);
  __ st_d(R0, FP, frame::interpreter_frame_last_sp_offset * wordSize);



  __ li(AT, JavaThread::popframe_inactive);
  __ st_w(AT, TREG, in_bytes(JavaThread::popframe_condition_offset()));

  // Finish with popframe handling
  __ restore_bcp();
  __ restore_locals();
  __ get_method(Rmethod);
  __ get_dispatch();

  // The method data pointer was incremented already during
  // call profiling. We have to restore the mdp for the current bcp.
  if (ProfileInterpreter) {
    __ set_method_data_pointer_for_bcp();
  }

  // Clear the popframe condition flag
  __ li(AT, JavaThread::popframe_inactive);
  __ st_w(AT, TREG, in_bytes(JavaThread::popframe_condition_offset()));

#if INCLUDE_JVMTI
  {
    Label L_done;

    __ ld_bu(AT, BCP, 0);
    __ addi_d(AT, AT, -1 * Bytecodes::_invokestatic);
    __ bne(AT, R0, L_done);

    // The member name argument must be restored if _invokestatic is re-executed after a PopFrame call.
    // Detect such a case in the InterpreterRuntime function and return the member name argument, or null.

    __ ld_d(T8, LVP, 0);
    __ call_VM(T8, CAST_FROM_FN_PTR(address, InterpreterRuntime::member_name_arg_or_null), T8, Rmethod, BCP);

    __ beq(T8, R0, L_done);

    __ st_d(T8, SP, 0);
    __ bind(L_done);
  }
#endif // INCLUDE_JVMTI

  __ dispatch_next(vtos);
  // end of PopFrame support

  Interpreter::_remove_activation_entry = __ pc();

  // preserve exception over this code sequence
  __ pop(T0);
  __ st_d(T0, TREG, in_bytes(JavaThread::vm_result_offset()));
  // remove the activation (without doing throws on illegalMonitorExceptions)
  __ remove_activation(vtos, false, true, false);
  // restore exception
  __ get_vm_result(T0, TREG);

  // In between activations - previous activation type unknown yet
  // compute continuation point - the continuation point expects
  // the following registers set up:
  //
  // T0: exception
  // RA: return address/pc that threw exception
  // SP: expression stack of caller
  // FP: fp of caller
  __ push2(T0, RA);             // save exception and return address
  __ super_call_VM_leaf(CAST_FROM_FN_PTR(address,
                        SharedRuntime::exception_handler_for_return_address), TREG, RA);
  __ move(T4, A0);              // save exception handler
  __ pop2(A0, A1);              // restore return address and exception

  // Note that an "issuing PC" is actually the next PC after the call
  __ jr(T4);                    // jump to exception handler of caller
}


//
// JVMTI ForceEarlyReturn support
//
address TemplateInterpreterGenerator::generate_earlyret_entry_for(TosState state) {
  address entry = __ pc();

  __ restore_bcp();
  __ restore_locals();
  __ empty_expression_stack();
  __ load_earlyret_value(state);

  __ ld_d(T4, Address(TREG, JavaThread::jvmti_thread_state_offset()));
  const Address cond_addr(T4, in_bytes(JvmtiThreadState::earlyret_state_offset()));

  // Clear the earlyret state
  __ li(AT, JvmtiThreadState::earlyret_inactive);
  __ st_w(AT, cond_addr);

  __ remove_activation(state,
                       false, /* throw_monitor_exception */
                       false, /* install_monitor_exception */
                       true); /* notify_jvmdi */
  __ jr(RA);

  return entry;
} // end of ForceEarlyReturn support


//-----------------------------------------------------------------------------
// Helper for vtos entry point generation

void TemplateInterpreterGenerator::set_vtos_entry_points(Template* t,
                                                         address& bep,
                                                         address& cep,
                                                         address& sep,
                                                         address& aep,
                                                         address& iep,
                                                         address& lep,
                                                         address& fep,
                                                         address& dep,
                                                         address& vep) {
  assert(t->is_valid() && t->tos_in() == vtos, "illegal template");
  Label L;
  aep = __ pc();     // atos entry point
      __ push(atos);
      __ b(L);
  fep = __ pc();     // ftos entry point
      __ push(ftos);
      __ b(L);
  dep = __ pc();     // dtos entry point
      __ push(dtos);
      __ b(L);
  lep = __ pc();     // ltos entry point
      __ push(ltos);
      __ b(L);
  bep = cep = sep = iep = __ pc();     // [bcsi]tos entry point
      __ push(itos);
  vep = __ pc();     // vtos entry point
  __ bind(L);
  generate_and_dispatch(t);
}

//-----------------------------------------------------------------------------

// Non-product code
#ifndef PRODUCT
address TemplateInterpreterGenerator::generate_trace_code(TosState state) {
  address entry = __ pc();

  // prepare expression stack
  __ push(state);       // save tosca

  // tos & tos2
  // trace_bytecode need actually 4 args, the last two is tos&tos2
  // this work fine for x86. but LA ABI calling convention will store A2-A3
  // to the stack position it think is the tos&tos2
  // when the expression stack have no more than 2 data, error occur.
  __ ld_d(A2, SP, 0);
  __ ld_d(A3, SP, 1 * wordSize);

  // pass arguments & call tracer
  __ call_VM(noreg, CAST_FROM_FN_PTR(address, InterpreterRuntime::trace_bytecode), RA, A2, A3);
  __ move(RA, V0);    // make sure return address is not destroyed by pop(state)

  // restore expression stack
  __ pop(state);        // restore tosca

  // return
  __ jr(RA);
  return entry;
}

void TemplateInterpreterGenerator::count_bytecode() {
  __ li(T8, (long)&BytecodeCounter::_counter_value);
  __ ld_w(AT, T8, 0);
  __ addi_d(AT, AT, 1);
  __ st_w(AT, T8, 0);
}

void TemplateInterpreterGenerator::histogram_bytecode(Template* t) {
  __ li(T8, (long)&BytecodeHistogram::_counters[t->bytecode()]);
  __ ld_w(AT, T8, 0);
  __ addi_d(AT, AT, 1);
  __ st_w(AT, T8, 0);
}

void TemplateInterpreterGenerator::histogram_bytecode_pair(Template* t) {
  __ li(T8, (long)&BytecodePairHistogram::_index);
  __ ld_w(T4, T8, 0);
  __ srli_d(T4, T4, BytecodePairHistogram::log2_number_of_codes);
  __ li(T8, ((long)t->bytecode()) << BytecodePairHistogram::log2_number_of_codes);
  __ orr(T4, T4, T8);
  __ li(T8, (long)&BytecodePairHistogram::_index);
  __ st_w(T4, T8, 0);
  __ slli_d(T4, T4, 2);
  __ li(T8, (long)BytecodePairHistogram::_counters);
  __ add_d(T8, T8, T4);
  __ ld_w(AT, T8, 0);
  __ addi_d(AT, AT, 1);
  __ st_w(AT, T8, 0);
}


void TemplateInterpreterGenerator::trace_bytecode(Template* t) {
  // Call a little run-time stub to avoid blow-up for each bytecode.
  // The run-time runtime saves the right registers, depending on
  // the tosca in-state for the given template.
  address entry = Interpreter::trace_code(t->tos_in());
  assert(entry != nullptr, "entry must have been generated");
  __ call(entry, relocInfo::none);
  //add for compressedoops
  __ reinit_heapbase();
}


void TemplateInterpreterGenerator::stop_interpreter_at() {
  Label L;
  __ li(T8, long(&BytecodeCounter::_counter_value));
  __ ld_w(T8, T8, 0);
  __ li(AT, StopInterpreterAt);
  __ bne(T8, AT, L);
  __ brk(5);
  __ bind(L);
}
#endif // !PRODUCT
