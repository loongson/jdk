/*
 * Copyright (c) 2018, Oracle and/or its affiliates. All rights reserved.
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
#include "asm/macroAssembler.inline.hpp"
#include "gc/g1/g1BarrierSet.hpp"
#include "gc/g1/g1BarrierSetAssembler.hpp"
#include "gc/g1/g1BarrierSetRuntime.hpp"
#include "gc/g1/g1CardTable.hpp"
#include "gc/g1/g1HeapRegion.hpp"
#include "gc/g1/g1ThreadLocalData.hpp"
#include "interpreter/interp_masm.hpp"
#include "runtime/sharedRuntime.hpp"
#include "utilities/macros.hpp"
#ifdef COMPILER1
#include "c1/c1_LIRAssembler.hpp"
#include "c1/c1_MacroAssembler.hpp"
#include "gc/g1/c1/g1BarrierSetC1.hpp"
#endif // COMPILER1
#ifdef COMPILER2
#include "gc/g1/c2/g1BarrierSetC2.hpp"
#endif // COMPILER2

#define __ masm->

void G1BarrierSetAssembler::gen_write_ref_array_pre_barrier(MacroAssembler* masm, DecoratorSet decorators,
                                                            Register addr, Register count, RegSet saved_regs) {
  bool dest_uninitialized = (decorators & IS_DEST_UNINITIALIZED) != 0;

  if (!dest_uninitialized) {
    Label filtered;
    Address in_progress(TREG, in_bytes(G1ThreadLocalData::satb_mark_queue_active_offset()));
    // Is marking active?
    if (in_bytes(SATBMarkQueue::byte_width_of_active()) == 4) {
      __ ld_w(AT, in_progress);
    } else {
      assert(in_bytes(SATBMarkQueue::byte_width_of_active()) == 1, "Assumption");
      __ ld_b(AT, in_progress);
    }

    __ beqz(AT, filtered);

    __ push(saved_regs);
    if (count == A0) {
      if (addr == A1) {
        __ move(AT, A0);
        __ move(A0, A1);
        __ move(A1, AT);
      } else {
        __ move(A1, count);
        __ move(A0, addr);
      }
    } else {
      __ move(A0, addr);
      __ move(A1, count);
    }
    if (UseCompressedOops) {
      __ call_VM_leaf(CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_array_pre_narrow_oop_entry), 2);
    } else {
      __ call_VM_leaf(CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_array_pre_oop_entry), 2);
    }
    __ pop(saved_regs);

    __ bind(filtered);
  }
}

void G1BarrierSetAssembler::gen_write_ref_array_post_barrier(MacroAssembler* masm, DecoratorSet decorators,
                                                             Register addr, Register count, Register tmp, RegSet saved_regs) {
  __ push(saved_regs);
  if (count == A0) {
    assert_different_registers(A1, addr);
    __ move(A1, count);
    __ move(A0, addr);
  } else {
    assert_different_registers(A0, count);
    __ move(A0, addr);
    __ move(A1, count);
  }
  __ call_VM_leaf(CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_array_post_entry), 2);
  __ pop(saved_regs);
}

void G1BarrierSetAssembler::load_at(MacroAssembler* masm, DecoratorSet decorators, BasicType type,
                                    Register dst, Address src, Register tmp1, Register tmp2) {
  bool on_oop = is_reference_type(type);
  bool on_weak = (decorators & ON_WEAK_OOP_REF) != 0;
  bool on_phantom = (decorators & ON_PHANTOM_OOP_REF) != 0;
  bool on_reference = on_weak || on_phantom;
  ModRefBarrierSetAssembler::load_at(masm, decorators, type, dst, src, tmp1, tmp2);
  if (on_oop && on_reference) {
    // RA is live. It must be saved around calls.
    __ enter(); // barrier may call runtime
    // Generate the G1 pre-barrier code to log the value of
    // the referent field in an SATB buffer.
    g1_write_barrier_pre(masm /* masm */,
                         noreg /* obj */,
                         dst /* pre_val */,
                         TREG /* thread */,
                         tmp1 /* tmp1 */,
                         tmp2 /* tmp2 */,
                         true /* tosca_live */,
                         true /* expand_call */);
    __ leave();
  }
}

static void generate_queue_test_and_insertion(MacroAssembler* masm, ByteSize index_offset, ByteSize buffer_offset, Label& runtime,
                                              const Register thread, const Register value, const Register tmp1, const Register tmp2) {
  // Can we store a value in the given thread's buffer?
  // (The index field is typed as size_t.)
  __ ld_d(tmp1, Address(thread, in_bytes(index_offset)));  // tmp1 := *(index address)
  __ beqz(tmp1, runtime);                                  // jump to runtime if index == 0 (full buffer)
  // The buffer is not full, store value into it.
  __ addi_d(tmp1, tmp1, -wordSize);                        // tmp1 := next index
  __ st_d(tmp1, Address(thread, in_bytes(index_offset)));  // *(index address) := next index
  __ ld_d(tmp2, Address(thread, in_bytes(buffer_offset))); // tmp2 := buffer address
  __ stx_d(value, tmp2, tmp1);                             // *(buffer address + next index) := value
}

static void generate_pre_barrier_fast_path(MacroAssembler* masm,
                                           const Register thread,
                                           const Register tmp1) {
  Address in_progress(thread, in_bytes(G1ThreadLocalData::satb_mark_queue_active_offset()));
  // Is marking active?
  if (in_bytes(SATBMarkQueue::byte_width_of_active()) == 4) {
    __ ld_wu(tmp1, in_progress);
  } else {
    assert(in_bytes(SATBMarkQueue::byte_width_of_active()) == 1, "Assumption");
    __ ld_bu(tmp1, in_progress);
  }
}

static void generate_pre_barrier_slow_path(MacroAssembler* masm,
                                           const Register obj,
                                           const Register pre_val,
                                           const Register thread,
                                           const Register tmp1,
                                           const Register tmp2,
                                           Label& done,
                                           Label& runtime) {
  // Do we need to load the previous value?
  if (obj != noreg) {
    __ load_heap_oop(pre_val, Address(obj, 0), noreg, noreg, AS_RAW);
  }
  // Is the previous value null?
  __ beqz(pre_val, done);
  generate_queue_test_and_insertion(masm,
                                    G1ThreadLocalData::satb_mark_queue_index_offset(),
                                    G1ThreadLocalData::satb_mark_queue_buffer_offset(),
                                    runtime,
                                    thread, pre_val, tmp1, tmp2);
  __ b(done);
}

void G1BarrierSetAssembler::g1_write_barrier_pre(MacroAssembler* masm,
                                                 Register obj,
                                                 Register pre_val,
                                                 Register thread,
                                                 Register tmp1,
                                                 Register tmp2,
                                                 bool tosca_live,
                                                 bool expand_call) {
  // If expand_call is true then we expand the call_VM_leaf macro
  // directly to skip generating the check by
  // InterpreterMacroAssembler::call_VM_leaf_base that checks _last_sp.

  assert(thread == TREG, "must be");

  Label done;
  Label runtime;

  assert_different_registers(obj, pre_val, tmp1, tmp2);
  assert(pre_val != noreg && tmp1 != noreg && tmp2 != noreg, "expecting a register");

  generate_pre_barrier_fast_path(masm, thread, tmp1);
  // If marking is not active (*(mark queue active address) == 0), jump to done
  __ beqz(tmp1, done);
  generate_pre_barrier_slow_path(masm, obj, pre_val, thread, tmp1, tmp2, done, runtime);

  __ bind(runtime);

  __ push_call_clobbered_registers();

  // Calling the runtime using the regular call_VM_leaf mechanism generates
  // code (generated by InterpreterMacroAssember::call_VM_leaf_base)
  // that checks that the *(ebp+frame::interpreter_frame_last_sp) == nullptr.
  //
  // If we care generating the pre-barrier without a frame (e.g. in the
  // intrinsified Reference.get() routine) then ebp might be pointing to
  // the caller frame and so this check will most likely fail at runtime.
  //
  // Expanding the call directly bypasses the generation of the check.
  // So when we do not have have a full interpreter frame on the stack
  // expand_call should be passed true.

  if (expand_call) {
    assert(pre_val != A1, "smashed arg");
    __ super_call_VM_leaf(CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_field_pre_entry), pre_val, thread);
  } else {
    __ call_VM_leaf(CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_field_pre_entry), pre_val, thread);
  }

  __ pop_call_clobbered_registers();

  __ bind(done);
}

static void generate_post_barrier_fast_path(MacroAssembler* masm,
                                            const Register store_addr,
                                            const Register new_val,
                                            const Register tmp1,
                                            const Register tmp2,
                                            Label& done,
                                            bool new_val_may_be_null) {
  // Does store cross heap regions?
  __ xorr(tmp1, store_addr, new_val);                      // tmp1 := store address ^ new value
  __ srli_d(tmp1, tmp1, G1HeapRegion::LogOfHRGrainBytes);  // tmp1 := ((store address ^ new value) >> LogOfHRGrainBytes)
  __ beqz(tmp1, done);
  // Crosses regions, storing null?
  if (new_val_may_be_null) {
    __ beqz(new_val, done);
  }
  // Storing region crossing non-null, is card young?
  __ srli_d(tmp1, store_addr, CardTable::card_shift());    // tmp1 := card address relative to card table base
  __ load_byte_map_base(tmp2);                             // tmp2 := card table base address
  __ add_d(tmp1, tmp1, tmp2);                              // tmp1 := card address
  __ ld_bu(tmp2, Address(tmp1));                           // tmp2 := card
}

static void generate_post_barrier_slow_path(MacroAssembler* masm,
                                            const Register thread,
                                            const Register tmp1,
                                            const Register tmp2,
                                            Label& done,
                                            Label& runtime) {
  __ membar(MacroAssembler::StoreLoad);  // StoreLoad membar
  __ ld_bu(tmp2, Address(tmp1));         // tmp2 := card
  __ beqz(tmp2, done);
  // Storing a region crossing, non-null oop, card is clean.
  // Dirty card and log.
  STATIC_ASSERT(CardTable::dirty_card_val() == 0);
  __ st_b(R0, Address(tmp1));       // *(card address) := dirty_card_val
  generate_queue_test_and_insertion(masm,
                                    G1ThreadLocalData::dirty_card_queue_index_offset(),
                                    G1ThreadLocalData::dirty_card_queue_buffer_offset(),
                                    runtime,
                                    thread, tmp1, tmp2, AT);
  __ b(done);
}

void G1BarrierSetAssembler::g1_write_barrier_post(MacroAssembler* masm,
                                                  Register store_addr,
                                                  Register new_val,
                                                  Register thread,
                                                  Register tmp1,
                                                  Register tmp2) {
  assert(thread == TREG, "must be");
  assert_different_registers(store_addr, thread, tmp1, tmp2, SCR1);
  assert(store_addr != noreg && new_val != noreg && tmp1 != noreg && tmp2 != noreg,
         "expecting a register");

  Label done;
  Label runtime;

  generate_post_barrier_fast_path(masm, store_addr, new_val, tmp1, tmp2, done, true /* new_val_may_be_null */);
  // If card is young, jump to done (tmp2 holds the card value)
  __ li(AT, (int)G1CardTable::g1_young_card_val());
  __ beq(tmp2, AT, done);   // card == young_card_val?
  generate_post_barrier_slow_path(masm, thread, tmp1, tmp2, done, runtime);

  __ bind(runtime);
  // save the live input values
  RegSet saved = RegSet::of(store_addr);
  __ push(saved);
  __ call_VM_leaf(CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_field_post_entry), tmp1, thread);
  __ pop(saved);

  __ bind(done);
}

#if defined(COMPILER2)

static void generate_c2_barrier_runtime_call(MacroAssembler* masm, G1BarrierStubC2* stub, const Register arg, const address runtime_path) {
  SaveLiveRegisters save_registers(masm, stub);
  if (c_rarg0 != arg) {
    __ move(c_rarg0, arg);
  }
  __ move(c_rarg1, TREG);
  __ li(AT, runtime_path);
  __ jalr(AT);
}

void G1BarrierSetAssembler::g1_write_barrier_pre_c2(MacroAssembler* masm,
                                                    Register obj,
                                                    Register pre_val,
                                                    Register thread,
                                                    Register tmp1,
                                                    Register tmp2,
                                                    G1PreBarrierStubC2* stub) {
  assert(thread == TREG, "must be");
  assert_different_registers(obj, pre_val, tmp1, tmp2);
  assert(pre_val != noreg && tmp1 != noreg && tmp2 != noreg, "expecting a register");

  stub->initialize_registers(obj, pre_val, thread, tmp1, tmp2);

  generate_pre_barrier_fast_path(masm, thread, tmp1);
  // If marking is active (*(mark queue active address) != 0), jump to stub (slow path)
  __ bnez(tmp1, *stub->entry());

  __ bind(*stub->continuation());
}

void G1BarrierSetAssembler::generate_c2_pre_barrier_stub(MacroAssembler* masm,
                                                         G1PreBarrierStubC2* stub) const {
  Assembler::InlineSkippedInstructionsCounter skip_counter(masm);
  Label runtime;
  Register obj = stub->obj();
  Register pre_val = stub->pre_val();
  Register thread = stub->thread();
  Register tmp1 = stub->tmp1();
  Register tmp2 = stub->tmp2();

  __ bind(*stub->entry());
  generate_pre_barrier_slow_path(masm, obj, pre_val, thread, tmp1, tmp2, *stub->continuation(), runtime);

  __ bind(runtime);
  generate_c2_barrier_runtime_call(masm, stub, pre_val, CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_field_pre_entry));
  __ b(*stub->continuation());
}

void G1BarrierSetAssembler::g1_write_barrier_post_c2(MacroAssembler* masm,
                                                     Register store_addr,
                                                     Register new_val,
                                                     Register thread,
                                                     Register tmp1,
                                                     Register tmp2,
                                                     G1PostBarrierStubC2* stub) {
  assert(thread == TREG, "must be");
  assert_different_registers(store_addr, new_val, thread, tmp1, tmp2, AT);
  assert(store_addr != noreg && new_val != noreg && tmp1 != noreg && tmp2 != noreg,
         "expecting a register");

  stub->initialize_registers(thread, tmp1, tmp2);

  bool new_val_may_be_null = (stub->barrier_data() & G1C2BarrierPostNotNull) == 0;
  generate_post_barrier_fast_path(masm, store_addr, new_val, tmp1, tmp2, *stub->continuation(), new_val_may_be_null);
  // If card is not young, jump to stub (slow path) (tmp2 holds the card value)
  __ li(AT, (int)G1CardTable::g1_young_card_val());
  __ sub_d(AT, tmp2, AT);
  __ bnez(AT, *stub->entry());

  __ bind(*stub->continuation());
}

void G1BarrierSetAssembler::generate_c2_post_barrier_stub(MacroAssembler* masm,
                                                          G1PostBarrierStubC2* stub) const {
  Assembler::InlineSkippedInstructionsCounter skip_counter(masm);
  Label runtime;
  Register thread = stub->thread();
  Register tmp1 = stub->tmp1(); // tmp1 holds the card address.
  Register tmp2 = stub->tmp2();

  __ bind(*stub->entry());
  generate_post_barrier_slow_path(masm, thread, tmp1, tmp2, *stub->continuation(), runtime);

  __ bind(runtime);
  generate_c2_barrier_runtime_call(masm, stub, tmp1, CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_field_post_entry));
  __ b(*stub->continuation());
}

#endif // COMPILER2

void G1BarrierSetAssembler::oop_store_at(MacroAssembler* masm, DecoratorSet decorators, BasicType type,
                                         Address dst, Register val, Register tmp1, Register tmp2, Register tmp3) {
  bool in_heap = (decorators & IN_HEAP) != 0;
  bool as_normal = (decorators & AS_NORMAL) != 0;
  assert((decorators & IS_DEST_UNINITIALIZED) == 0, "unsupported");

  bool needs_pre_barrier = as_normal;
  bool needs_post_barrier = val != noreg && in_heap;

  // flatten object address if needed
  // We do it regardless of precise because we need the registers
  if (dst.index() == noreg && dst.disp() == 0) {
    if (dst.base() != tmp3) {
      __ move(tmp3, dst.base());
    }
  } else {
    __ lea(tmp3, dst);
  }

  if (needs_pre_barrier) {
    g1_write_barrier_pre(masm /*masm*/,
                         tmp3 /* obj */,
                         tmp2 /* pre_val */,
                         TREG /* thread */,
                         tmp1  /* tmp1 */,
                         SCR1  /* tmp2 */,
                         val != noreg /* tosca_live */,
                         false /* expand_call */);
  }
  if (val == noreg) {
    BarrierSetAssembler::store_at(masm, decorators, type, Address(tmp3, 0), val, noreg, noreg, noreg);
  } else {
    Register new_val = val;
    if (needs_post_barrier) {
      // G1 barrier needs uncompressed oop for region cross check.
      if (UseCompressedOops) {
        new_val = tmp2;
        __ move(new_val, val);
      }
    }
    BarrierSetAssembler::store_at(masm, decorators, type, Address(tmp3, 0), val, noreg, noreg, noreg);
    if (needs_post_barrier) {
      g1_write_barrier_post(masm /*masm*/,
                            tmp3 /* store_adr */,
                            new_val /* new_val */,
                            TREG /* thread */,
                            tmp1 /* tmp1 */,
                            tmp2 /* tmp2 */);
    }
  }
}

#ifdef COMPILER1

#undef __
#define __ ce->masm()->

void G1BarrierSetAssembler::gen_pre_barrier_stub(LIR_Assembler* ce, G1PreBarrierStub* stub) {
  G1BarrierSetC1* bs = (G1BarrierSetC1*)BarrierSet::barrier_set()->barrier_set_c1();
  // At this point we know that marking is in progress.
  // If do_load() is true then we have to emit the
  // load of the previous value; otherwise it has already
  // been loaded into _pre_val.

  __ bind(*stub->entry());

  assert(stub->pre_val()->is_register(), "Precondition.");

  Register pre_val_reg = stub->pre_val()->as_register();

  if (stub->do_load()) {
    ce->mem2reg(stub->addr(), stub->pre_val(), T_OBJECT, stub->patch_code(), stub->info(), false /*wide*/);
  }
  __ beqz(pre_val_reg, *stub->continuation());
  ce->store_parameter(stub->pre_val()->as_register(), 0);
  __ call(bs->pre_barrier_c1_runtime_code_blob()->code_begin(), relocInfo::runtime_call_type);
  __ b(*stub->continuation());
}

void G1BarrierSetAssembler::gen_post_barrier_stub(LIR_Assembler* ce, G1PostBarrierStub* stub) {
  G1BarrierSetC1* bs = (G1BarrierSetC1*)BarrierSet::barrier_set()->barrier_set_c1();
  __ bind(*stub->entry());
  assert(stub->addr()->is_register(), "Precondition.");
  assert(stub->new_val()->is_register(), "Precondition.");
  Register new_val_reg = stub->new_val()->as_register();
  __ beqz(new_val_reg, *stub->continuation());
  ce->store_parameter(stub->addr()->as_pointer_register(), 0);
  __ call(bs->post_barrier_c1_runtime_code_blob()->code_begin(), relocInfo::runtime_call_type);
  __ b(*stub->continuation());
}

#undef __

#define __ sasm->

void G1BarrierSetAssembler::generate_c1_pre_barrier_runtime_stub(StubAssembler* sasm) {
  __ prologue("g1_pre_barrier", false);

  // arg0 : previous value of memory

  BarrierSet* bs = BarrierSet::barrier_set();

  const Register pre_val = A0;
  const Register tmp = SCR2;

  Address in_progress(TREG, in_bytes(G1ThreadLocalData::satb_mark_queue_active_offset()));
  Address queue_index(TREG, in_bytes(G1ThreadLocalData::satb_mark_queue_index_offset()));
  Address buffer(TREG, in_bytes(G1ThreadLocalData::satb_mark_queue_buffer_offset()));

  Label done;
  Label runtime;

  // Is marking still active?
  if (in_bytes(SATBMarkQueue::byte_width_of_active()) == 4) {  // 4-byte width
    __ ld_w(tmp, in_progress);
  } else {
    assert(in_bytes(SATBMarkQueue::byte_width_of_active()) == 1, "Assumption");
    __ ld_b(tmp, in_progress);
  }
  __ beqz(tmp, done);

  // Can we store original value in the thread's buffer?
  __ ld_d(tmp, queue_index);
  __ beqz(tmp, runtime);

  __ addi_d(tmp, tmp, -wordSize);
  __ st_d(tmp, queue_index);
  __ ld_d(SCR1, buffer);
  __ add_d(tmp, tmp, SCR1);
  __ load_parameter(0, SCR1);
  __ st_d(SCR1, Address(tmp, 0));
  __ b(done);

  __ bind(runtime);
  __ push_call_clobbered_registers();
  __ load_parameter(0, pre_val);
  __ call_VM_leaf(CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_field_pre_entry), pre_val, TREG);
  __ pop_call_clobbered_registers();
  __ bind(done);

  __ epilogue();
}

void G1BarrierSetAssembler::generate_c1_post_barrier_runtime_stub(StubAssembler* sasm) {
  __ prologue("g1_post_barrier", false);

  // arg0: store_address, not use?
  Address store_addr(FP, 2 * BytesPerWord);

  BarrierSet* bs = BarrierSet::barrier_set();
  CardTableBarrierSet* ctbs = barrier_set_cast<CardTableBarrierSet>(bs);
  CardTable* ct = ctbs->card_table();

  Label done;
  Label runtime;

  // At this point we know new_value is non-null and the new_value crosses regions.
  // Must check to see if card is already dirty

  Address queue_index(TREG, in_bytes(G1ThreadLocalData::dirty_card_queue_index_offset()));
  Address buffer(TREG, in_bytes(G1ThreadLocalData::dirty_card_queue_buffer_offset()));

  const Register card_offset = SCR2;
  // RA is free here, so we can use it to hold the byte_map_base.
  const Register byte_map_base = RA;

  assert_different_registers(card_offset, byte_map_base, SCR1);

  __ load_parameter(0, card_offset);
  __ srli_d(card_offset, card_offset, CardTable::card_shift());
  __ load_byte_map_base(byte_map_base);
  __ ldx_bu(SCR1, byte_map_base, card_offset);
  __ addi_d(SCR1, SCR1, -(int)G1CardTable::g1_young_card_val());
  __ beqz(SCR1, done);

  assert((int)CardTable::dirty_card_val() == 0, "must be 0");

  __ membar(Assembler::StoreLoad);
  __ ldx_bu(SCR1, byte_map_base, card_offset);
  __ beqz(SCR1, done);

  // storing region crossing non-null, card is clean.
  // dirty card and log.
  __ stx_b(R0, byte_map_base, card_offset);

  // Convert card offset into an address in card_addr
  Register card_addr = card_offset;
  __ add_d(card_addr, byte_map_base, card_addr);

  __ ld_d(SCR1, queue_index);
  __ beqz(SCR1, runtime);
  __ addi_d(SCR1, SCR1, -wordSize);
  __ st_d(SCR1, queue_index);

  // Reuse RA to hold buffer_addr
  const Register buffer_addr = RA;

  __ ld_d(buffer_addr, buffer);
  __ stx_d(card_addr, buffer_addr, SCR1);
  __ b(done);

  __ bind(runtime);
  __ push_call_clobbered_registers();
  __ call_VM_leaf(CAST_FROM_FN_PTR(address, G1BarrierSetRuntime::write_ref_field_post_entry), card_addr, TREG);
  __ pop_call_clobbered_registers();
  __ bind(done);
  __ epilogue();
}

#undef __

#endif // COMPILER1
