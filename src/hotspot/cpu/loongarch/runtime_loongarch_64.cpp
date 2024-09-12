/*
 * Copyright (c) 2024, 2024, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2024, Loongson Technology. All rights reserved.
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
#ifdef COMPILER2
#include "asm/macroAssembler.hpp"
#include "asm/macroAssembler.inline.hpp"
#include "code/vmreg.hpp"
#include "interpreter/interpreter.hpp"
#include "opto/runtime.hpp"
#include "runtime/interfaceSupport.inline.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/stubRoutines.hpp"
#include "runtime/vframeArray.hpp"
#include "utilities/globalDefinitions.hpp"
#include "vmreg_loongarch.inline.hpp"

#define __ masm->

//------------------------------generate_uncommon_trap_blob--------------------
void OptoRuntime::generate_uncommon_trap_blob() {
  // Allocate space for the code
  ResourceMark rm;
  // Setup code generation tools
  CodeBuffer buffer("uncommon_trap_blob", 2048, 1024);
  MacroAssembler* masm = new MacroAssembler(&buffer);

  enum frame_layout {
    fp_off, fp_off2,
    return_off, return_off2,
    framesize
  };
  assert(framesize % 4 == 0, "sp not 16-byte aligned");

  address start = __ pc();

  // Push self-frame.
  __ addi_d(SP, SP, -framesize * BytesPerInt);
  __ st_d(RA, SP, return_off * BytesPerInt);
  __ st_d(FP, SP, fp_off * BytesPerInt);
  // we don't expect an arg reg save area
#ifndef PRODUCT
  assert(frame::arg_reg_save_area_bytes == 0, "not expecting frame reg save area");
#endif
  // compiler left unloaded_class_index in j_rarg0 move to where the
  // runtime expects it.
  __ addi_w(c_rarg1, j_rarg0, 0);

  // we need to set the past SP to the stack pointer of the stub frame
  // and the pc to the address where this runtime call will return
  // although actually any pc in this code blob will do).
  Label retaddr;
  __ set_last_Java_frame(noreg, noreg, retaddr);

  // Call C code. We cannot block on this call, no GC can happen.
  // Call should capture callee-saved registers as well as return values.
  //
  // UnrollBlock* uncommon_trap(JavaThread* thread, jint unloaded_class_index, jint exec_mode)
  //
  __ move(c_rarg0, TREG);
  __ addi_w(c_rarg2, R0, (unsigned)Deoptimization::Unpack_uncommon_trap);
  __ call(CAST_FROM_FN_PTR(address, Deoptimization::uncommon_trap),
          relocInfo::runtime_call_type);
  __ bind(retaddr);

  // Set an oopmap for the call site
  OopMapSet *oop_maps = new OopMapSet();

  oop_maps->add_gc_map(__ pc() - start, new OopMap(framesize, 0));

  __ reset_last_Java_frame(false);

  Register unroll = T8;
  Register pcs    = T6;
  Register sizes  = T5;
  Register count  = T4;

  __ move(unroll, c_rarg0); // move call return value to unroll

#ifdef ASSERT
  { Label L;
    __ ld_d(AT, Address(unroll, Deoptimization::UnrollBlock::unpack_kind_offset()));
    __ li(T4, Deoptimization::Unpack_uncommon_trap);
    __ beq(AT, T4, L);
    __ stop("OptoRuntime::generate_uncommon_trap_blob: expected Unpack_uncommon_trap");
    __ bind(L);
  }
#endif

  // Pop all the frames we must move/replace.
  //
  // Frame picture (youngest to oldest)
  // 1: self-frame (no frame link)
  // 2: deopting frame  (no frame link)
  // 3: caller of deopting frame (could be compiled/interpreted).

  __ addi_d(SP, SP, framesize << LogBytesPerInt);

  // Pop deoptimized frame (int)
  __ ld_wu(AT, Address(unroll, Deoptimization::UnrollBlock::size_of_deoptimized_frame_offset()));
  __ add_d(SP, SP, AT);
  // LoongArch do not need to restore RA and FP here, since:
  // 1: The RA shall be loaded by frame PC array (frame_pcs) later
  // 2: The FP is protected via frame::initial_deoptimization_info()

#ifdef ASSERT
  // Compilers generate code that bang the stack by as much as the
  // interpreter would need. So this stack banging should never
  // trigger a fault. Verify that it does not on non product builds.
  __ ld_wu(sizes, Address(unroll, Deoptimization::UnrollBlock::total_frame_sizes_offset()));
  __ bang_stack_size(sizes, pcs /* tmp */);
#endif

  __ ld_d(pcs, Address(unroll, Deoptimization::UnrollBlock::frame_pcs_offset()));
  __ ld_d(sizes, Address(unroll, Deoptimization::UnrollBlock::frame_sizes_offset()));
  __ ld_wu(count, Address(unroll, Deoptimization::UnrollBlock::number_of_frames_offset()));

  // Pick up the initial fp we should save
  __ ld_d(FP, Address(unroll, Deoptimization::UnrollBlock::initial_info_offset()));

  // Now adjust the caller's stack to make up for the extra locals but
  // record the original sp so that we can save it in the skeletal
  // interpreter frame and the stack walking of interpreter_sender
  // will get the unextended sp value and not the "real" sp value.

  __ move(Rsender, SP);
  __ ld_wu(AT, Address(unroll, Deoptimization::UnrollBlock::caller_adjustment_offset()));
  __ sub_d(SP, SP, AT);

  // Push interpreter frames in a loop
  Label loop;
  __ bind(loop);
  __ ld_d(AT, sizes, 0);            // load frame size
  __ ld_d(RA, pcs, 0);              // save return address
  __ addi_d(AT, AT, -2 * wordSize); // we'll push RA and FP, by hand
  __ enter();
  __ sub_d(SP, SP, AT);
  // Save Rsender to make it walkable, and then pass it to next frame.
  __ st_d(Rsender, FP, frame::interpreter_frame_sender_sp_offset * wordSize);
  __ move(Rsender, SP);
  // This value is corrected by layout_activation_impl
  __ st_d(R0, FP, frame::interpreter_frame_last_sp_offset * wordSize);
  __ addi_d(count, count, -1);
  __ addi_d(sizes, sizes, wordSize);
  __ addi_d(pcs, pcs, wordSize);
  __ blt(R0, count, loop);

  __ ld_d(RA, pcs, 0); // save final return address

  __ enter();

  // Use FP because the frames look interpreted now. Save "the_pc" since it
  // cannot easily be retrieved using the last_java_SP after we aligned SP.
  // Do not need the precise return PC address here, just precise enough to
  // point into this code blob.
  Label L;
  address the_pc = __ pc();
  __ bind(L);
  __ set_last_Java_frame(SP, FP, L);

  assert(StackAlignmentInBytes == 16, "must be");
  __ bstrins_d(SP, R0, 3, 0);

  // Call C code. We cannot block on this call, no GC can happen.
  // Call should capture callee-saved registers as well as return values.
  //
  // BasicType unpack_frames(JavaThread* thread, int exec_mode)
  //
  __ move(c_rarg0, TREG);
  __ addi_w(c_rarg1, R0, (unsigned)Deoptimization::Unpack_uncommon_trap);
  __ call(CAST_FROM_FN_PTR(address, Deoptimization::unpack_frames),
          relocInfo::runtime_call_type);

  // Set an oopmap for the call site
  // Use the same PC we used for the last java frame
  oop_maps->add_gc_map(the_pc - start, new OopMap(framesize, 0));

  __ reset_last_Java_frame(true);

  __ leave();
  __ jr(RA);

  // make sure all code is generated
  masm->flush();

  _uncommon_trap_blob = UncommonTrapBlob::create(&buffer, oop_maps, framesize >> 1);
}

//-------------- generate_exception_blob -----------
// creates exception blob at the end
// Using exception blob, this code is jumped from a compiled method.
// (see emit_exception_handler in loongarch.ad file)
//
// Given an exception pc at a call we call into the runtime for the
// handler in this method. This handler might merely restore state
// (i.e. callee save registers) unwind the frame and jump to the
// exception handler for the nmethod if there is no Java level handler
// for the nmethod.
//
// This code is entered with a jump, and left with a jump.
//
// Arguments:
//   A0: exception oop
//   A1: exception pc
//
// Results:
//   A0: exception oop
//   A1: exception pc in caller
//   destination: exception handler of caller
//
// Note: the exception pc MUST be at a call (precise debug information)
//
//  [stubGenerator_loongarch_64.cpp] generate_forward_exception()
//      |- A0, A1 are created
//      |- T4 <= SharedRuntime::exception_handler_for_return_address
//      `- jr T4
//           `- the caller's exception_handler
//                 `- jr OptoRuntime::exception_blob
//                        `- here
//
void OptoRuntime::generate_exception_blob() {
  enum frame_layout {
    fp_off, fp_off2,
    return_off, return_off2,
    framesize
  };
  assert(framesize % 4 == 0, "sp not 16-byte aligned");

  // Allocate space for the code
  ResourceMark rm;
  // Setup code generation tools
  CodeBuffer buffer("exception_blob", 2048, 1024);
  MacroAssembler* masm = new MacroAssembler(&buffer);

  address start = __ pc();

  // Exception pc is 'return address' for stack walker
  __ push2(A1 /* return address */, FP);

  // there are no callee save registers and we don't expect an
  // arg reg save area
#ifndef PRODUCT
  assert(frame::arg_reg_save_area_bytes == 0, "not expecting frame reg save area");
#endif
  // Store exception in Thread object. We cannot pass any arguments to the
  // handle_exception call, since we do not want to make any assumption
  // about the size of the frame where the exception happened in.
  __ st_d(A0, Address(TREG, JavaThread::exception_oop_offset()));
  __ st_d(A1, Address(TREG, JavaThread::exception_pc_offset()));

  // This call does all the hard work.  It checks if an exception handler
  // exists in the method.
  // If so, it returns the handler address.
  // If not, it prepares for stack-unwinding, restoring the callee-save
  // registers of the frame being removed.
  //
  // address OptoRuntime::handle_exception_C(JavaThread* thread)
  //
  Label L;
  address the_pc = __ pc();
  __ bind(L);
  __ set_last_Java_frame(TREG, SP, NOREG, L);

  assert(StackAlignmentInBytes == 16, "must be");
  __ bstrins_d(SP, R0, 3, 0);   // Fix stack alignment as required by ABI

  __ move(A0, TREG);
  __ call(CAST_FROM_FN_PTR(address, OptoRuntime::handle_exception_C),
          relocInfo::runtime_call_type);

  // handle_exception_C is a special VM call which does not require an explicit
  // instruction sync afterwards.

  // Set an oopmap for the call site.  This oopmap will only be used if we
  // are unwinding the stack.  Hence, all locations will be dead.
  // Callee-saved registers will be the same as the frame above (i.e.,
  // handle_exception_stub), since they were restored when we got the
  // exception.

  OopMapSet *oop_maps = new OopMapSet();

  oop_maps->add_gc_map(the_pc - start, new OopMap(framesize, 0));

  __ reset_last_Java_frame(TREG, false);

  // Restore callee-saved registers

  // FP is an implicitly saved callee saved register (i.e. the calling
  // convention will save restore it in prolog/epilog) Other than that
  // there are no callee save registers now that adapter frames are gone.
  // and we dont' expect an arg reg save area
  __ pop2(RA, FP);

  const Register exception_handler = T4;

  // We have a handler in A0, (could be deopt blob)
  __ move(exception_handler, A0);

  // Get the exception
  __ ld_d(A0, Address(TREG, JavaThread::exception_oop_offset()));
  // Get the exception pc in case we are deoptimized
  __ ld_d(A1, Address(TREG, JavaThread::exception_pc_offset()));
#ifdef ASSERT
  __ st_d(R0, Address(TREG, JavaThread::exception_handler_pc_offset()));
  __ st_d(R0, Address(TREG, JavaThread::exception_pc_offset()));
#endif
  // Clear the exception oop so GC no longer processes it as a root.
  __ st_d(R0, Address(TREG, JavaThread::exception_oop_offset()));

  // A0: exception oop
  // A1: exception pc
  __ jr(exception_handler);

  // make sure all code is generated
  masm->flush();

  // Set exception blob
  _exception_blob = ExceptionBlob::create(&buffer, oop_maps, framesize >> 1);
}
#endif // COMPILER2
