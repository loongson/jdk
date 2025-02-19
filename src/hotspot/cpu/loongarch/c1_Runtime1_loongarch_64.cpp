/*
 * Copyright (c) 1999, 2021, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2021, 2025, Loongson Technology. All rights reserved.
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
#include "asm/assembler.hpp"
#include "c1/c1_CodeStubs.hpp"
#include "c1/c1_Defs.hpp"
#include "c1/c1_MacroAssembler.hpp"
#include "c1/c1_Runtime1.hpp"
#include "compiler/disassembler.hpp"
#include "compiler/oopMap.hpp"
#include "gc/shared/cardTable.hpp"
#include "gc/shared/cardTableBarrierSet.hpp"
#include "gc/shared/collectedHeap.hpp"
#include "gc/shared/tlab_globals.hpp"
#include "interpreter/interpreter.hpp"
#include "memory/universe.hpp"
#include "nativeInst_loongarch.hpp"
#include "oops/oop.inline.hpp"
#include "prims/jvmtiExport.hpp"
#include "register_loongarch.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/signature.hpp"
#include "runtime/stubRoutines.hpp"
#include "runtime/vframe.hpp"
#include "runtime/vframeArray.hpp"
#include "utilities/powerOfTwo.hpp"
#include "vmreg_loongarch.inline.hpp"

// Implementation of StubAssembler

int StubAssembler::call_RT(Register oop_result1, Register metadata_result, address entry, int args_size) {
  // setup registers
  assert(!(oop_result1->is_valid() || metadata_result->is_valid()) || oop_result1 != metadata_result,
         "registers must be different");
  assert(oop_result1 != TREG && metadata_result != TREG, "registers must be different");
  assert(args_size >= 0, "illegal args_size");
  bool align_stack = false;

  move(A0, TREG);
  set_num_rt_args(0); // Nothing on stack

  Label retaddr;
  set_last_Java_frame(SP, FP, retaddr);

  // do the call
  call(entry, relocInfo::runtime_call_type);
  bind(retaddr);
  int call_offset = offset();
  // verify callee-saved register
#ifdef ASSERT
  { Label L;
    get_thread(SCR1);
    beq(TREG, SCR1, L);
    stop("StubAssembler::call_RT: TREG not callee saved?");
    bind(L);
  }
#endif
  reset_last_Java_frame(true);

  // check for pending exceptions
  { Label L;
    // check for pending exceptions (java_thread is set upon return)
    ld_d(SCR1, Address(TREG, Thread::pending_exception_offset()));
    beqz(SCR1, L);
    // exception pending => remove activation and forward to exception handler
    // make sure that the vm_results are cleared
    if (oop_result1->is_valid()) {
      st_d(R0, Address(TREG, JavaThread::vm_result_offset()));
    }
    if (metadata_result->is_valid()) {
      st_d(R0, Address(TREG, JavaThread::vm_result_2_offset()));
    }
    if (frame_size() == no_frame_size) {
      leave();
      jmp(StubRoutines::forward_exception_entry(), relocInfo::runtime_call_type);
    } else if (_stub_id == (int)C1StubId::forward_exception_id) {
      should_not_reach_here();
    } else {
      jmp(Runtime1::entry_for(C1StubId::forward_exception_id), relocInfo::runtime_call_type);
    }
    bind(L);
  }
  // get oop results if there are any and reset the values in the thread
  if (oop_result1->is_valid()) {
    get_vm_result(oop_result1, TREG);
  }
  if (metadata_result->is_valid()) {
    get_vm_result_2(metadata_result, TREG);
  }
  return call_offset;
}

int StubAssembler::call_RT(Register oop_result1, Register metadata_result,
                           address entry, Register arg1) {
  move(A1, arg1);
  return call_RT(oop_result1, metadata_result, entry, 1);
}

int StubAssembler::call_RT(Register oop_result1, Register metadata_result,
                           address entry, Register arg1, Register arg2) {
  if (A1 == arg2) {
    if (A2 == arg1) {
      move(SCR1, arg1);
      move(arg1, arg2);
      move(arg2, SCR1);
    } else {
      move(A2, arg2);
      move(A1, arg1);
    }
  } else {
    move(A1, arg1);
    move(A2, arg2);
  }
  return call_RT(oop_result1, metadata_result, entry, 2);
}

int StubAssembler::call_RT(Register oop_result1, Register metadata_result,
                           address entry, Register arg1, Register arg2, Register arg3) {
  // if there is any conflict use the stack
  if (arg1 == A2 || arg1 == A3 ||
      arg2 == A1 || arg2 == A3 ||
      arg3 == A1 || arg3 == A2) {
    addi_d(SP, SP, -4 * wordSize);
    st_d(arg1, Address(SP, 0 * wordSize));
    st_d(arg2, Address(SP, 1 * wordSize));
    st_d(arg3, Address(SP, 2 * wordSize));
    ld_d(arg1, Address(SP, 0 * wordSize));
    ld_d(arg2, Address(SP, 1 * wordSize));
    ld_d(arg3, Address(SP, 2 * wordSize));
    addi_d(SP, SP, 4 * wordSize);
  } else {
    move(A1, arg1);
    move(A2, arg2);
    move(A3, arg3);
  }
  return call_RT(oop_result1, metadata_result, entry, 3);
}

enum return_state_t {
  does_not_return, requires_return, requires_pop_epilogue_return
};

// Implementation of StubFrame

class StubFrame: public StackObj {
 private:
  StubAssembler* _sasm;
  return_state_t _return_state;

 public:
  StubFrame(StubAssembler* sasm, const char* name, bool must_gc_arguments,
            return_state_t return_state=requires_return);
  void load_argument(int offset_in_words, Register reg);

  ~StubFrame();
};;

void StubAssembler::prologue(const char* name, bool must_gc_arguments) {
  set_info(name, must_gc_arguments);
  enter();
}

void StubAssembler::epilogue(bool use_pop) {
  // Avoid using a leave instruction when this frame may
  // have been frozen, since the current value of fp
  // restored from the stub would be invalid. We still
  // must restore the fp value saved on enter though.
  if (use_pop) {
    pop2(RA, FP);
  } else {
    leave();
  }
  jr(RA);
}

#define __ _sasm->

StubFrame::StubFrame(StubAssembler* sasm, const char* name, bool must_gc_arguments,
                     return_state_t return_state) {
  _sasm = sasm;
  _return_state = return_state;
  __ prologue(name, must_gc_arguments);
}

// load parameters that were stored with LIR_Assembler::store_parameter
// Note: offsets for store_parameter and load_argument must match
void StubFrame::load_argument(int offset_in_words, Register reg) {
  __ load_parameter(offset_in_words, reg);
}

StubFrame::~StubFrame() {
  if (_return_state == does_not_return) {
    __ should_not_reach_here();
  } else {
    __ epilogue(_return_state == requires_pop_epilogue_return);
  }
  _sasm = nullptr;
}

#undef __

// Implementation of Runtime1

#define __ sasm->

// Stack layout for saving/restoring  all the registers needed during a runtime
// call (this includes deoptimization)
// Note: note that users of this frame may well have arguments to some runtime
// while these values are on the stack. These positions neglect those arguments
// but the code in save_live_registers will take the argument count into
// account.
//

enum reg_save_layout {
  reg_save_frame_size = 32 /* float */ + 30 /* integer, except zr, tp */
};

// Save off registers which might be killed by calls into the runtime.
// Tries to smart of about FP registers.  In particular we separate
// saving and describing the FPU registers for deoptimization since we
// have to save the FPU registers twice if we describe them.  The
// deopt blob is the only thing which needs to describe FPU registers.
// In all other cases it should be sufficient to simply save their
// current value.

static int cpu_reg_save_offsets[FrameMap::nof_cpu_regs];
static int fpu_reg_save_offsets[FrameMap::nof_fpu_regs];
static int reg_save_size_in_words;
static int frame_size_in_bytes = -1;

static OopMap* generate_oop_map(StubAssembler* sasm, bool save_fpu_registers) {
  int frame_size_in_bytes = reg_save_frame_size * BytesPerWord;
  sasm->set_frame_size(frame_size_in_bytes / BytesPerWord);
  int frame_size_in_slots = frame_size_in_bytes / VMRegImpl::stack_slot_size;
  OopMap* oop_map = new OopMap(frame_size_in_slots, 0);

  for (int i = A0->encoding(); i <= T8->encoding(); i++) {
    Register r = as_Register(i);
    if (i != SCR1->encoding() && i != SCR2->encoding()) {
      int sp_offset = cpu_reg_save_offsets[i];
      oop_map->set_callee_saved(VMRegImpl::stack2reg(sp_offset), r->as_VMReg());
    }
  }

  int sp_offset = cpu_reg_save_offsets[TREG->encoding()];
  oop_map->set_callee_saved(VMRegImpl::stack2reg(sp_offset),
                            TREG->as_VMReg());

  // fpu_regs
  if (save_fpu_registers) {
    for (int i = 0; i < FrameMap::nof_fpu_regs; i++) {
      FloatRegister r = as_FloatRegister(i);
      int sp_offset = fpu_reg_save_offsets[i];
      oop_map->set_callee_saved(VMRegImpl::stack2reg(sp_offset), r->as_VMReg());
    }
  }

  return oop_map;
}

static OopMap* save_live_registers(StubAssembler* sasm,
                                   bool save_fpu_registers = true) {
  __ block_comment("save_live_registers");

  // integer registers except zr & ra & tp & sp & rx. 4 is due to alignment.
  __ addi_d(SP, SP, -(32 - 4 + 32) * wordSize);

  for (int i = 4; i < 21; i++)
    __ st_d(as_Register(i), Address(SP, (32 + i - 4) * wordSize));
  for (int i = 22; i < 32; i++)
    __ st_d(as_Register(i), Address(SP, (32 + i - 4) * wordSize));

  if (save_fpu_registers) {
    for (int i = 0; i < 32; i++)
      __ fst_d(as_FloatRegister(i), Address(SP, i * wordSize));
  }

  return generate_oop_map(sasm, save_fpu_registers);
}

static void restore_live_registers(StubAssembler* sasm, bool restore_fpu_registers = true) {
  if (restore_fpu_registers) {
    for (int i = 0; i < 32; i ++)
      __ fld_d(as_FloatRegister(i), Address(SP, i * wordSize));
  }

  for (int i = 4; i < 21; i++)
    __ ld_d(as_Register(i), Address(SP, (32 + i - 4) * wordSize));
  for (int i = 22; i < 32; i++)
    __ ld_d(as_Register(i), Address(SP, (32 + i - 4) * wordSize));

  __ addi_d(SP, SP, (32 - 4 + 32) * wordSize);
}

static void restore_live_registers_except_a0(StubAssembler* sasm, bool restore_fpu_registers = true)  {
  if (restore_fpu_registers) {
    for (int i = 0; i < 32; i ++)
      __ fld_d(as_FloatRegister(i), Address(SP, i * wordSize));
  }

  for (int i = 5; i < 21; i++)
    __ ld_d(as_Register(i), Address(SP, (32 + i - 4) * wordSize));
  for (int i = 22; i < 32; i++)
    __ ld_d(as_Register(i), Address(SP, (32 + i - 4) * wordSize));

  __ addi_d(SP, SP, (32 - 4 + 32) * wordSize);
}

void Runtime1::initialize_pd() {
  int sp_offset = 0;
  int i;

  // all float registers are saved explicitly
  assert(FrameMap::nof_fpu_regs == 32, "double registers not handled here");
  for (i = 0; i < FrameMap::nof_fpu_regs; i++) {
    fpu_reg_save_offsets[i] = sp_offset;
    sp_offset += 2; // SP offsets are in halfwords
  }

  for (i = 4; i < FrameMap::nof_cpu_regs; i++) {
    Register r = as_Register(i);
    cpu_reg_save_offsets[i] = sp_offset;
    sp_offset += 2; // SP offsets are in halfwords
  }
}

// return: offset in 64-bit words.
uint Runtime1::runtime_blob_current_thread_offset(frame f) {
  CodeBlob* cb = f.cb();
  assert(cb == Runtime1::blob_for(C1StubId::monitorenter_id) ||
         cb == Runtime1::blob_for(C1StubId::monitorenter_nofpu_id), "must be");
  assert(cb != nullptr && cb->is_runtime_stub(), "invalid frame");
  int offset = cpu_reg_save_offsets[TREG->encoding()];
  return offset / 2;   // SP offsets are in halfwords
}

// target: the entry point of the method that creates and posts the exception oop
// has_argument: true if the exception needs arguments (passed in SCR1 and SCR2)

OopMapSet* Runtime1::generate_exception_throw(StubAssembler* sasm, address target,
                                              bool has_argument) {
  // make a frame and preserve the caller's caller-save registers
  OopMap* oop_map = save_live_registers(sasm);
  int call_offset;
  if (!has_argument) {
    call_offset = __ call_RT(noreg, noreg, target);
  } else {
    __ move(A1, SCR1);
    __ move(A2, SCR2);
    call_offset = __ call_RT(noreg, noreg, target);
  }
  OopMapSet* oop_maps = new OopMapSet();
  oop_maps->add_gc_map(call_offset, oop_map);
  return oop_maps;
}

OopMapSet* Runtime1::generate_handle_exception(C1StubId id, StubAssembler *sasm) {
  __ block_comment("generate_handle_exception");

  // incoming parameters
  const Register exception_oop = A0;
  const Register exception_pc  = A1;
  // other registers used in this stub

  // Save registers, if required.
  OopMapSet* oop_maps = new OopMapSet();
  OopMap* oop_map = nullptr;
  switch (id) {
  case C1StubId::forward_exception_id:
    // We're handling an exception in the context of a compiled frame.
    // The registers have been saved in the standard places.  Perform
    // an exception lookup in the caller and dispatch to the handler
    // if found.  Otherwise unwind and dispatch to the callers
    // exception handler.
    oop_map = generate_oop_map(sasm, 1 /*thread*/);

    // load and clear pending exception oop into A0
    __ ld_d(exception_oop, Address(TREG, Thread::pending_exception_offset()));
    __ st_d(R0, Address(TREG, Thread::pending_exception_offset()));

    // load issuing PC (the return address for this stub) into A1
    __ ld_d(exception_pc, Address(FP, frame::return_addr_offset * BytesPerWord));

    // make sure that the vm_results are cleared (may be unnecessary)
    __ st_d(R0, Address(TREG, JavaThread::vm_result_offset()));
    __ st_d(R0, Address(TREG, JavaThread::vm_result_2_offset()));
    break;
  case C1StubId::handle_exception_nofpu_id:
  case C1StubId::handle_exception_id:
    // At this point all registers MAY be live.
    oop_map = save_live_registers(sasm, id != C1StubId::handle_exception_nofpu_id);
    break;
  case C1StubId::handle_exception_from_callee_id: {
    // At this point all registers except exception oop (A0) and
    // exception pc (RA) are dead.
    const int frame_size = 2 /*fp, return address*/;
    oop_map = new OopMap(frame_size * VMRegImpl::slots_per_word, 0);
    sasm->set_frame_size(frame_size);
    break;
  }
  default: ShouldNotReachHere();
  }

  // verify that only A0 and A1 are valid at this time
  __ invalidate_registers(false, true, true, true, true, true);
  // verify that A0 contains a valid exception
  __ verify_not_null_oop(exception_oop);

#ifdef ASSERT
  // check that fields in JavaThread for exception oop and issuing pc are
  // empty before writing to them
  Label oop_empty;
  __ ld_d(SCR1, Address(TREG, JavaThread::exception_oop_offset()));
  __ beqz(SCR1, oop_empty);
  __ stop("exception oop already set");
  __ bind(oop_empty);

  Label pc_empty;
  __ ld_d(SCR1, Address(TREG, JavaThread::exception_pc_offset()));
  __ beqz(SCR1, pc_empty);
  __ stop("exception pc already set");
  __ bind(pc_empty);
#endif

  // save exception oop and issuing pc into JavaThread
  // (exception handler will load it from here)
  __ st_d(exception_oop, Address(TREG, JavaThread::exception_oop_offset()));
  __ st_d(exception_pc, Address(TREG, JavaThread::exception_pc_offset()));

  // patch throwing pc into return address (has bci & oop map)
  __ st_d(exception_pc, Address(FP, frame::return_addr_offset * BytesPerWord));

  // compute the exception handler.
  // the exception oop and the throwing pc are read from the fields in JavaThread
  int call_offset = __ call_RT(noreg, noreg, CAST_FROM_FN_PTR(address, exception_handler_for_pc));
  oop_maps->add_gc_map(call_offset, oop_map);

  // A0: handler address
  //      will be the deopt blob if nmethod was deoptimized while we looked up
  //      handler regardless of whether handler existed in the nmethod.

  // only A0 is valid at this time, all other registers have been destroyed by the runtime call
  __ invalidate_registers(false, true, true, true, true, true);

  // patch the return address, this stub will directly return to the exception handler
  __ st_d(A0, Address(FP, frame::return_addr_offset * BytesPerWord));

  switch (id) {
    case C1StubId::forward_exception_id:
    case C1StubId::handle_exception_nofpu_id:
    case C1StubId::handle_exception_id:
      // Restore the registers that were saved at the beginning.
      restore_live_registers(sasm, id != C1StubId::handle_exception_nofpu_id);
      break;
    case C1StubId::handle_exception_from_callee_id:
      break;
    default:  ShouldNotReachHere();
  }

  return oop_maps;
}

void Runtime1::generate_unwind_exception(StubAssembler *sasm) {
  // incoming parameters
  const Register exception_oop = A0;
  // callee-saved copy of exception_oop during runtime call
  const Register exception_oop_callee_saved = S0;
  // other registers used in this stub
  const Register exception_pc = A1;
  const Register handler_addr = A3;

  if (AbortVMOnException) {
    __ enter();
    save_live_registers(sasm);
    __ call_VM_leaf(CAST_FROM_FN_PTR(address, check_abort_on_vm_exception), A0);
    restore_live_registers(sasm);
    __ leave();
  }

  // verify that only A0, is valid at this time
  __ invalidate_registers(false, true, true, true, true, true);

#ifdef ASSERT
  // check that fields in JavaThread for exception oop and issuing pc are empty
  Label oop_empty;
  __ ld_d(SCR1, Address(TREG, JavaThread::exception_oop_offset()));
  __ beqz(SCR1, oop_empty);
  __ stop("exception oop must be empty");
  __ bind(oop_empty);

  Label pc_empty;
  __ ld_d(SCR1, Address(TREG, JavaThread::exception_pc_offset()));
  __ beqz(SCR1, pc_empty);
  __ stop("exception pc must be empty");
  __ bind(pc_empty);
#endif

  // Save our return address because
  // exception_handler_for_return_address will destroy it.  We also
  // save exception_oop
  __ addi_d(SP, SP, -2 * wordSize);
  __ st_d(RA, Address(SP, 0 * wordSize));
  __ st_d(exception_oop, Address(SP, 1 * wordSize));

  // search the exception handler address of the caller (using the return address)
  __ call_VM_leaf(CAST_FROM_FN_PTR(address, SharedRuntime::exception_handler_for_return_address), TREG, RA);
  // V0: exception handler address of the caller

  // Only V0 is valid at this time; all other registers have been
  // destroyed by the call.
  __ invalidate_registers(false, true, true, true, false, true);

  // move result of call into correct register
  __ move(handler_addr, A0);

  // get throwing pc (= return address).
  // RA has been destroyed by the call
  __ ld_d(RA, Address(SP, 0 * wordSize));
  __ ld_d(exception_oop, Address(SP, 1 * wordSize));
  __ addi_d(SP, SP, 2 * wordSize);
  __ move(A1, RA);

  __ verify_not_null_oop(exception_oop);

  // continue at exception handler (return address removed)
  // note: do *not* remove arguments when unwinding the
  //       activation since the caller assumes having
  //       all arguments on the stack when entering the
  //       runtime to determine the exception handler
  //       (GC happens at call site with arguments!)
  // A0: exception oop
  // A1: throwing pc
  // A3: exception handler
  __ jr(handler_addr);
}

OopMapSet* Runtime1::generate_patching(StubAssembler* sasm, address target) {
  // use the maximum number of runtime-arguments here because it is difficult to
  // distinguish each RT-Call.
  // Note: This number affects also the RT-Call in generate_handle_exception because
  //       the oop-map is shared for all calls.
  DeoptimizationBlob* deopt_blob = SharedRuntime::deopt_blob();
  assert(deopt_blob != nullptr, "deoptimization blob must have been created");

  OopMap* oop_map = save_live_registers(sasm);

  __ move(A0, TREG);
  Label retaddr;
  __ set_last_Java_frame(SP, FP, retaddr);
  // do the call
  __ call(target, relocInfo::runtime_call_type);
  __ bind(retaddr);
  OopMapSet* oop_maps = new OopMapSet();
  oop_maps->add_gc_map(__ offset(), oop_map);
  // verify callee-saved register
#ifdef ASSERT
  { Label L;
    __ get_thread(SCR1);
    __ beq(TREG, SCR1, L);
    __ stop("StubAssembler::call_RT: TREG not callee saved?");
    __ bind(L);
  }
#endif

  __ reset_last_Java_frame(true);

#ifdef ASSERT
  // check that fields in JavaThread for exception oop and issuing pc are empty
  Label oop_empty;
  __ ld_d(SCR1, Address(TREG, Thread::pending_exception_offset()));
  __ beqz(SCR1, oop_empty);
  __ stop("exception oop must be empty");
  __ bind(oop_empty);

  Label pc_empty;
  __ ld_d(SCR1, Address(TREG, JavaThread::exception_pc_offset()));
  __ beqz(SCR1, pc_empty);
  __ stop("exception pc must be empty");
  __ bind(pc_empty);
#endif

  // Runtime will return true if the nmethod has been deoptimized, this is the
  // expected scenario and anything else is  an error. Note that we maintain a
  // check on the result purely as a defensive measure.
  Label no_deopt;
  __ beqz(A0, no_deopt); // Have we deoptimized?

  // Perform a re-execute. The proper return  address is already on the stack,
  // we just need  to restore registers, pop  all of our frame  but the return
  // address and jump to the deopt blob.
  restore_live_registers(sasm);
  __ leave();
  __ jmp(deopt_blob->unpack_with_reexecution(), relocInfo::runtime_call_type);

  __ bind(no_deopt);
  __ stop("deopt not performed");

  return oop_maps;
}

OopMapSet* Runtime1::generate_code_for(C1StubId id, StubAssembler* sasm) {
  // for better readability
  const bool must_gc_arguments = true;
  const bool dont_gc_arguments = false;

  // default value; overwritten for some optimized stubs that are called
  // from methods that do not use the fpu
  bool save_fpu_registers = true;

  // stub code & info for the different stubs
  OopMapSet* oop_maps = nullptr;
  OopMap* oop_map = nullptr;
  switch (id) {
    {
    case C1StubId::forward_exception_id:
      {
        oop_maps = generate_handle_exception(id, sasm);
        __ leave();
        __ jr(RA);
      }
      break;

    case C1StubId::throw_div0_exception_id:
      {
        StubFrame f(sasm, "throw_div0_exception", dont_gc_arguments, does_not_return);
        oop_maps = generate_exception_throw(sasm, CAST_FROM_FN_PTR(address, throw_div0_exception), false);
      }
      break;

    case C1StubId::throw_null_pointer_exception_id:
      {
        StubFrame f(sasm, "throw_null_pointer_exception", dont_gc_arguments, does_not_return);
        oop_maps = generate_exception_throw(sasm, CAST_FROM_FN_PTR(address, throw_null_pointer_exception), false);
      }
      break;

    case C1StubId::new_instance_id:
    case C1StubId::fast_new_instance_id:
    case C1StubId::fast_new_instance_init_check_id:
      {
        Register klass = A3; // Incoming
        Register obj   = A0; // Result

        if (id == C1StubId::new_instance_id) {
          __ set_info("new_instance", dont_gc_arguments);
        } else if (id == C1StubId::fast_new_instance_id) {
          __ set_info("fast new_instance", dont_gc_arguments);
        } else {
          assert(id == C1StubId::fast_new_instance_init_check_id, "bad StubID");
          __ set_info("fast new_instance init check", dont_gc_arguments);
        }

        __ enter();
        OopMap* map = save_live_registers(sasm);
        int call_offset = __ call_RT(obj, noreg, CAST_FROM_FN_PTR(address, new_instance), klass);
        oop_maps = new OopMapSet();
        oop_maps->add_gc_map(call_offset, map);
        restore_live_registers_except_a0(sasm);
        __ verify_oop(obj);
        __ leave();
        __ jr(RA);

        // A0,: new instance
      }

      break;

    case C1StubId::counter_overflow_id:
      {
        Register bci = A0, method = A1;
        __ enter();
        OopMap* map = save_live_registers(sasm);
        // Retrieve bci
        __ ld_w(bci, Address(FP, 0 * BytesPerWord));
        // And a pointer to the Method*
        __ ld_d(method, Address(FP, 1 * BytesPerWord));
        int call_offset = __ call_RT(noreg, noreg, CAST_FROM_FN_PTR(address, counter_overflow), bci, method);
        oop_maps = new OopMapSet();
        oop_maps->add_gc_map(call_offset, map);
        restore_live_registers(sasm);
        __ leave();
        __ jr(RA);
      }
      break;

    case C1StubId::new_type_array_id:
    case C1StubId::new_object_array_id:
      {
        Register length   = S0; // Incoming
        Register klass    = A3; // Incoming
        Register obj      = A0; // Result

        if (id == C1StubId::new_type_array_id) {
          __ set_info("new_type_array", dont_gc_arguments);
        } else {
          __ set_info("new_object_array", dont_gc_arguments);
        }

#ifdef ASSERT
        // assert object type is really an array of the proper kind
        {
          Label ok;
          Register t0 = obj;
          __ ld_w(t0, Address(klass, Klass::layout_helper_offset()));
          __ srai_w(t0, t0, Klass::_lh_array_tag_shift);
          int tag = ((id == C1StubId::new_type_array_id)
                     ? Klass::_lh_array_tag_type_value
                     : Klass::_lh_array_tag_obj_value);
          __ li(SCR1, tag);
          __ beq(t0, SCR1, ok);
          __ stop("assert(is an array klass)");
          __ should_not_reach_here();
          __ bind(ok);
        }
#endif // ASSERT

        __ enter();
        OopMap* map = save_live_registers(sasm);
        int call_offset;
        if (id == C1StubId::new_type_array_id) {
          call_offset = __ call_RT(obj, noreg, CAST_FROM_FN_PTR(address, new_type_array), klass, length);
        } else {
          call_offset = __ call_RT(obj, noreg, CAST_FROM_FN_PTR(address, new_object_array), klass, length);
        }

        oop_maps = new OopMapSet();
        oop_maps->add_gc_map(call_offset, map);
        restore_live_registers_except_a0(sasm);

        __ verify_oop(obj);
        __ leave();
        __ jr(RA);

        // A0: new array
      }
      break;

    case C1StubId::new_multi_array_id:
      {
        StubFrame f(sasm, "new_multi_array", dont_gc_arguments);
        // A0,: klass
        // S0,: rank
        // A2: address of 1st dimension
        OopMap* map = save_live_registers(sasm);
        __ move(A1, A0);
        __ move(A3, A2);
        __ move(A2, S0);
        int call_offset = __ call_RT(A0, noreg, CAST_FROM_FN_PTR(address, new_multi_array), A1, A2, A3);

        oop_maps = new OopMapSet();
        oop_maps->add_gc_map(call_offset, map);
        restore_live_registers_except_a0(sasm);

        // A0,: new multi array
        __ verify_oop(A0);
      }
      break;

    case C1StubId::register_finalizer_id:
      {
        __ set_info("register_finalizer", dont_gc_arguments);

        // This is called via call_runtime so the arguments
        // will be place in C abi locations

        __ verify_oop(A0);

        // load the klass and check the has finalizer flag
        Label register_finalizer;
        Register t = A5;
        __ load_klass(t, A0);
        __ ld_bu(t, Address(t, Klass::misc_flags_offset()));
        __ test_bit(SCR1, t, exact_log2(KlassFlags::_misc_has_finalizer));
        __ bnez(SCR1, register_finalizer);
        __ jr(RA);

        __ bind(register_finalizer);
        __ enter();
        OopMap* oop_map = save_live_registers(sasm);
        int call_offset = __ call_RT(noreg, noreg, CAST_FROM_FN_PTR(address, SharedRuntime::register_finalizer), A0);
        oop_maps = new OopMapSet();
        oop_maps->add_gc_map(call_offset, oop_map);

        // Now restore all the live registers
        restore_live_registers(sasm);

        __ leave();
        __ jr(RA);
      }
      break;

    case C1StubId::throw_class_cast_exception_id:
      {
        StubFrame f(sasm, "throw_class_cast_exception", dont_gc_arguments, does_not_return);
        oop_maps = generate_exception_throw(sasm, CAST_FROM_FN_PTR(address, throw_class_cast_exception), true);
      }
      break;

    case C1StubId::throw_incompatible_class_change_error_id:
      {
        StubFrame f(sasm, "throw_incompatible_class_cast_exception", dont_gc_arguments, does_not_return);
        oop_maps = generate_exception_throw(sasm, CAST_FROM_FN_PTR(address, throw_incompatible_class_change_error), false);
      }
      break;

    case C1StubId::slow_subtype_check_id:
      {
        // Typical calling sequence:
        // __ push(klass_RInfo);  // object klass or other subclass
        // __ push(sup_k_RInfo);  // array element klass or other superclass
        // __ bl(slow_subtype_check);
        // Note that the subclass is pushed first, and is therefore deepest.
        enum layout {
          a0_off, a0_off_hi,
          a2_off, a2_off_hi,
          a4_off, a4_off_hi,
          a5_off, a5_off_hi,
          sup_k_off, sup_k_off_hi,
          klass_off, klass_off_hi,
          framesize,
          result_off = sup_k_off
        };

        __ set_info("slow_subtype_check", dont_gc_arguments);
        __ addi_d(SP, SP, -4 * wordSize);
        __ st_d(A0, Address(SP, a0_off * VMRegImpl::stack_slot_size));
        __ st_d(A2, Address(SP, a2_off * VMRegImpl::stack_slot_size));
        __ st_d(A4, Address(SP, a4_off * VMRegImpl::stack_slot_size));
        __ st_d(A5, Address(SP, a5_off * VMRegImpl::stack_slot_size));

        // This is called by pushing args and not with C abi
        __ ld_d(A4, Address(SP, klass_off * VMRegImpl::stack_slot_size)); // subclass
        __ ld_d(A0, Address(SP, sup_k_off * VMRegImpl::stack_slot_size)); // superclass

        Label miss;
        __ check_klass_subtype_slow_path<false>(A4, A0, A2, A5, nullptr, &miss);

        // fallthrough on success:
        __ li(SCR1, 1);
        __ st_d(SCR1, Address(SP, result_off * VMRegImpl::stack_slot_size)); // result
        __ ld_d(A0, Address(SP, a0_off * VMRegImpl::stack_slot_size));
        __ ld_d(A2, Address(SP, a2_off * VMRegImpl::stack_slot_size));
        __ ld_d(A4, Address(SP, a4_off * VMRegImpl::stack_slot_size));
        __ ld_d(A5, Address(SP, a5_off * VMRegImpl::stack_slot_size));
        __ addi_d(SP, SP, 4 * wordSize);
        __ jr(RA);

        __ bind(miss);
        __ st_d(R0, Address(SP, result_off * VMRegImpl::stack_slot_size)); // result
        __ ld_d(A0, Address(SP, a0_off * VMRegImpl::stack_slot_size));
        __ ld_d(A2, Address(SP, a2_off * VMRegImpl::stack_slot_size));
        __ ld_d(A4, Address(SP, a4_off * VMRegImpl::stack_slot_size));
        __ ld_d(A5, Address(SP, a5_off * VMRegImpl::stack_slot_size));
        __ addi_d(SP, SP, 4 * wordSize);
        __ jr(RA);
      }
      break;

    case C1StubId::monitorenter_nofpu_id:
      save_fpu_registers = false;
      // fall through
    case C1StubId::monitorenter_id:
      {
        StubFrame f(sasm, "monitorenter", dont_gc_arguments, requires_pop_epilogue_return);
        OopMap* map = save_live_registers(sasm, save_fpu_registers);

        // Called with store_parameter and not C abi

        f.load_argument(1, A0); // A0,: object
        f.load_argument(0, A1); // A1,: lock address

        int call_offset = __ call_RT(noreg, noreg, CAST_FROM_FN_PTR(address, monitorenter), A0, A1);

        oop_maps = new OopMapSet();
        oop_maps->add_gc_map(call_offset, map);
        restore_live_registers(sasm, save_fpu_registers);
      }
      break;

    case C1StubId::monitorexit_nofpu_id:
      save_fpu_registers = false;
      // fall through
    case C1StubId::monitorexit_id:
      {
        StubFrame f(sasm, "monitorexit", dont_gc_arguments);
        OopMap* map = save_live_registers(sasm, save_fpu_registers);

        // Called with store_parameter and not C abi

        f.load_argument(0, A0); // A0,: lock address

        // note: really a leaf routine but must setup last java sp
        //       => use call_RT for now (speed can be improved by
        //       doing last java sp setup manually)
        int call_offset = __ call_RT(noreg, noreg, CAST_FROM_FN_PTR(address, monitorexit), A0);

        oop_maps = new OopMapSet();
        oop_maps->add_gc_map(call_offset, map);
        restore_live_registers(sasm, save_fpu_registers);
      }
      break;

    case C1StubId::deoptimize_id:
      {
        StubFrame f(sasm, "deoptimize", dont_gc_arguments, does_not_return);
        OopMap* oop_map = save_live_registers(sasm);
        f.load_argument(0, A1);
        int call_offset = __ call_RT(noreg, noreg, CAST_FROM_FN_PTR(address, deoptimize), A1);

        oop_maps = new OopMapSet();
        oop_maps->add_gc_map(call_offset, oop_map);
        restore_live_registers(sasm);
        DeoptimizationBlob* deopt_blob = SharedRuntime::deopt_blob();
        assert(deopt_blob != nullptr, "deoptimization blob must have been created");
        __ leave();
        __ jmp(deopt_blob->unpack_with_reexecution(), relocInfo::runtime_call_type);
      }
      break;

    case C1StubId::throw_range_check_failed_id:
      {
        StubFrame f(sasm, "range_check_failed", dont_gc_arguments, does_not_return);
        oop_maps = generate_exception_throw(sasm, CAST_FROM_FN_PTR(address, throw_range_check_exception), true);
      }
      break;

    case C1StubId::unwind_exception_id:
      {
        __ set_info("unwind_exception", dont_gc_arguments);
        // note: no stubframe since we are about to leave the current
        //       activation and we are calling a leaf VM function only.
        generate_unwind_exception(sasm);
      }
      break;

    case C1StubId::access_field_patching_id:
      {
        StubFrame f(sasm, "access_field_patching", dont_gc_arguments, does_not_return);
        // we should set up register map
        oop_maps = generate_patching(sasm, CAST_FROM_FN_PTR(address, access_field_patching));
      }
      break;

    case C1StubId::load_klass_patching_id:
      {
        StubFrame f(sasm, "load_klass_patching", dont_gc_arguments, does_not_return);
        // we should set up register map
        oop_maps = generate_patching(sasm, CAST_FROM_FN_PTR(address, move_klass_patching));
      }
      break;

    case C1StubId::load_mirror_patching_id:
      {
        StubFrame f(sasm, "load_mirror_patching", dont_gc_arguments, does_not_return);
        // we should set up register map
        oop_maps = generate_patching(sasm, CAST_FROM_FN_PTR(address, move_mirror_patching));
      }
      break;

    case C1StubId::load_appendix_patching_id:
      {
        StubFrame f(sasm, "load_appendix_patching", dont_gc_arguments, does_not_return);
        // we should set up register map
        oop_maps = generate_patching(sasm, CAST_FROM_FN_PTR(address, move_appendix_patching));
      }
      break;

    case C1StubId::handle_exception_nofpu_id:
    case C1StubId::handle_exception_id:
      {
        StubFrame f(sasm, "handle_exception", dont_gc_arguments);
        oop_maps = generate_handle_exception(id, sasm);
      }
      break;

    case C1StubId::handle_exception_from_callee_id:
      {
        StubFrame f(sasm, "handle_exception_from_callee", dont_gc_arguments);
        oop_maps = generate_handle_exception(id, sasm);
      }
      break;

    case C1StubId::throw_index_exception_id:
      {
        StubFrame f(sasm, "index_range_check_failed", dont_gc_arguments, does_not_return);
        oop_maps = generate_exception_throw(sasm, CAST_FROM_FN_PTR(address, throw_index_exception), true);
      }
      break;

    case C1StubId::throw_array_store_exception_id:
      {
        StubFrame f(sasm, "throw_array_store_exception", dont_gc_arguments, does_not_return);
        // tos + 0: link
        //     + 1: return address
        oop_maps = generate_exception_throw(sasm, CAST_FROM_FN_PTR(address, throw_array_store_exception), true);
      }
      break;

    case C1StubId::predicate_failed_trap_id:
      {
        StubFrame f(sasm, "predicate_failed_trap", dont_gc_arguments, does_not_return);

        OopMap* map = save_live_registers(sasm);

        int call_offset = __ call_RT(noreg, noreg, CAST_FROM_FN_PTR(address, predicate_failed_trap));
        oop_maps = new OopMapSet();
        oop_maps->add_gc_map(call_offset, map);
        restore_live_registers(sasm);
        __ leave();
        DeoptimizationBlob* deopt_blob = SharedRuntime::deopt_blob();
        assert(deopt_blob != nullptr, "deoptimization blob must have been created");

        __ jmp(deopt_blob->unpack_with_reexecution(), relocInfo::runtime_call_type);
      }
      break;

    case C1StubId::dtrace_object_alloc_id:
      {
        // A0: object
        StubFrame f(sasm, "dtrace_object_alloc", dont_gc_arguments);
        save_live_registers(sasm);

        __ call_VM_leaf(CAST_FROM_FN_PTR(address, static_cast<int (*)(oopDesc*)>(SharedRuntime::dtrace_object_alloc)), A0);

        restore_live_registers(sasm);
      }
      break;

    default:
      {
        StubFrame f(sasm, "unimplemented entry", dont_gc_arguments, does_not_return);
        __ li(A0, (int)id);
        __ call_RT(noreg, noreg, CAST_FROM_FN_PTR(address, unimplemented_entry), A0);
      }
      break;
    }
  }
  return oop_maps;
}

#undef __

const char *Runtime1::pd_name_for_address(address entry) {
  Unimplemented();
  return 0;
}
