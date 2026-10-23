/*
 * Copyright (c) 2018, 2021, Red Hat, Inc. All rights reserved.
 * Copyright (c) 2022, 2026, Loongson Technology. All rights reserved.
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

#include "gc/shenandoah/heuristics/shenandoahHeuristics.hpp"
#include "gc/shenandoah/mode/shenandoahMode.hpp"
#include "gc/shenandoah/shenandoahBarrierSet.hpp"
#include "gc/shenandoah/shenandoahBarrierSetAssembler.hpp"
#include "gc/shenandoah/shenandoahHeap.inline.hpp"
#include "gc/shenandoah/shenandoahHeapRegion.hpp"
#include "gc/shenandoah/shenandoahRuntime.hpp"
#include "gc/shenandoah/shenandoahThreadLocalData.hpp"
#include "interpreter/interp_masm.hpp"
#include "interpreter/interpreter.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/thread.hpp"
#ifdef COMPILER1
#include "c1/c1_LIRAssembler.hpp"
#include "c1/c1_MacroAssembler.hpp"
#include "gc/shenandoah/c1/shenandoahBarrierSetC1.hpp"
#endif
#ifdef COMPILER2
#include "gc/shenandoah/c2/shenandoahBarrierSetC2.hpp"
#include "opto/output.hpp"
#endif

#define __ masm->

void ShenandoahBarrierSetAssembler::arraycopy_prologue(MacroAssembler* masm, DecoratorSet decorators, bool is_oop,
                                                       Register src, Register dst, Register count, RegSet saved_regs) {
  if (is_oop) {
    bool dest_uninitialized = (decorators & IS_DEST_UNINITIALIZED) != 0;
    if ((ShenandoahSATBBarrier && !dest_uninitialized) || ShenandoahLoadRefBarrier) {
      Label done;

      // Avoid calling runtime if count == 0
      __ beqz(count, done);

      // Is GC active?
      assert(!saved_regs.contains(SCR1), "Sanity: about to clobber SCR1");
      Address gc_state(TREG, in_bytes(ShenandoahThreadLocalData::gc_state_offset()));
      __ ld_b(SCR1, gc_state);
      if (ShenandoahSATBBarrier && dest_uninitialized) {
        __ andi(SCR1, SCR1, ShenandoahHeap::HAS_FORWARDED);
        __ beqz(SCR1, done);
      } else {
        __ andi(SCR1, SCR1, ShenandoahHeap::HAS_FORWARDED | ShenandoahHeap::MARKING);
        __ beqz(SCR1, done);
      }

      __ push_call_clobbered_registers();
      // If arguments are not in proper places, shuffle them.
      // Doing this via the stack is the most straight-forward way to avoid
      // accidentally smashing any register.
      if (c_rarg0 != src || c_rarg1 != dst || c_rarg2 != count) {
        __ push(RegSet::of(src));
        __ push(RegSet::of(dst));
        __ push(RegSet::of(count));
        __ pop(RegSet::of(c_rarg2));
        __ pop(RegSet::of(c_rarg1));
        __ pop(RegSet::of(c_rarg0));
      }
      address target = nullptr;
      if (UseCompressedOops) {
        target = CAST_FROM_FN_PTR(address, ShenandoahRuntime::arraycopy_barrier_narrow_oop);
      } else {
        target = CAST_FROM_FN_PTR(address, ShenandoahRuntime::arraycopy_barrier_oop);
      }
      __ call_VM_leaf(target, 3);
      __ pop_call_clobbered_registers();
      __ bind(done);
    }
  }
}

void ShenandoahBarrierSetAssembler::arraycopy_epilogue(MacroAssembler* masm, DecoratorSet decorators, bool is_oop,
                                                       Register start, Register count, Register tmp) {
  if (ShenandoahCardBarrier && is_oop) {
    gen_write_ref_array_post_barrier(masm, decorators, start, count, tmp);
  }
}

void ShenandoahBarrierSetAssembler::satb_barrier(MacroAssembler* masm,
                                                 Register obj,
                                                 Register pre_val,
                                                 Register thread,
                                                 Register tmp1,
                                                 Register tmp2) {
  assert(ShenandoahSATBBarrier, "Should be checked by caller");
  assert(thread == TREG, "must be");

  Label done;
  Label runtime;

  assert_different_registers(obj, pre_val, tmp1, tmp2);
  assert(pre_val != noreg && tmp1 != noreg && tmp2 != noreg, "expecting a register");

  Address index(thread, in_bytes(ShenandoahThreadLocalData::satb_mark_queue_index_offset()));
  Address buffer(thread, in_bytes(ShenandoahThreadLocalData::satb_mark_queue_buffer_offset()));

  // Is marking active?
  Address gc_state(TREG, in_bytes(ShenandoahThreadLocalData::gc_state_offset()));
  __ ld_bu(tmp1, gc_state);
  __ test_bit(tmp1, tmp1, ShenandoahHeap::MARKING_BITPOS);
  __ beqz(tmp1, done);

  // Do we need to load the previous value?
  if (obj != noreg) {
    if (UseCompressedOops) {
      __ ld_wu(pre_val, Address(obj, 0));
      __ decode_heap_oop(pre_val);
    } else {
      __ ld_d(pre_val, Address(obj, 0));
    }
  }

  // Is the previous value null?
  __ beqz(pre_val, done);

  // Can we store original value in the thread's buffer?
  // Is index == 0?
  // (The index field is typed as size_t.)

  __ ld_d(tmp1, index);                     // tmp := *index_adr
  __ beqz(tmp1, runtime);                   // tmp == 0?
                                           // If yes, goto runtime

  __ addi_d(tmp1, tmp1, -wordSize);          // tmp := tmp - wordSize
  __ st_d(tmp1, index);                     // *index_adr := tmp
  __ ld_d(tmp2, buffer);
                                            // tmp := tmp + *buffer_adr

  // Record the previous value
  __ stx_d(pre_val, tmp1, tmp2);
  __ b(done);

  // Slow-path call.
  __ bind(runtime);
  __ enter();
  __ push_call_clobbered_registers();
  if (c_rarg0 != pre_val) {
    __ move(c_rarg0, pre_val);
  }

  // Calling with super_call_VM_leaf with c_rarg0 bypasses interpreter checks and avoids any moves.
  __ super_call_VM_leaf(CAST_FROM_FN_PTR(address, ShenandoahRuntime::write_barrier_pre), c_rarg0);
  __ pop_call_clobbered_registers();
  __ leave();

  __ bind(done);
}

void ShenandoahBarrierSetAssembler::load_reference_barrier(MacroAssembler* masm, Register dst, Address load_addr, DecoratorSet decorators) {
  assert(ShenandoahLoadRefBarrier, "Should be enabled");
  assert_different_registers(load_addr.base(), load_addr.index(), SCR1, SCR2);

  bool is_strong  = ShenandoahBarrierSet::is_strong_access(decorators);
  bool is_weak    = ShenandoahBarrierSet::is_weak_access(decorators);
  bool is_phantom = ShenandoahBarrierSet::is_phantom_access(decorators);
  bool is_native  = ShenandoahBarrierSet::is_native_access(decorators);
  bool is_narrow  = UseCompressedOops && !is_native;

  Label heap_stable, not_cset;
  Address gc_state(TREG, in_bytes(ShenandoahThreadLocalData::gc_state_offset()));
  Register tmp = (dst == SCR1) ? SCR2 : SCR1;

  // Check for heap stability
  if (is_strong) {
    __ ld_b(tmp, gc_state);
    __ andi(tmp, tmp, ShenandoahHeap::HAS_FORWARDED);
    __ beqz(tmp, heap_stable);
  } else {
    Label lrb;
    __ ld_b(tmp, gc_state);
    __ andi(tmp, tmp, ShenandoahHeap::WEAK_ROOTS);
    __ bnez(tmp, lrb);

    __ ld_b(tmp, gc_state);
    __ andi(tmp, tmp, ShenandoahHeap::HAS_FORWARDED);
    __ beqz(tmp, heap_stable);
    __ bind(lrb);
  }

  // use A1 for load address
  Register result_dst = dst;
  if (dst == A1) {
    __ move(tmp, dst);
    dst = tmp;
  }

  // Save A0 and A1, unless it is an output register
  __ push2(A0, A1);
  __ lea(A1, load_addr);
  __ move(A0, dst);

  // Test for in-cset
  if (is_strong) {
    __ li(SCR2, ShenandoahHeap::in_cset_fast_test_addr());
    __ srli_d(SCR1, A0, ShenandoahHeapRegion::region_size_bytes_shift_jint());
    __ ldx_b(SCR2, SCR2, SCR1);
    __ beqz(SCR2, not_cset);
  }

  // Slow-path call
  __ enter();
  __ bstrins_d(SP, R0, 3, 0);
  __ push_call_clobbered_registers_except(RegSet::of(V0));
  address target = nullptr;
  if (is_strong) {
    if (is_narrow) {
      target = CAST_FROM_FN_PTR(address, ShenandoahRuntime::load_reference_barrier_strong_narrow);
    } else {
      target = CAST_FROM_FN_PTR(address, ShenandoahRuntime::load_reference_barrier_strong);
    }
  } else if (is_weak) {
    if (is_narrow) {
      target = CAST_FROM_FN_PTR(address, ShenandoahRuntime::load_reference_barrier_weak_narrow);
    } else {
      target = CAST_FROM_FN_PTR(address, ShenandoahRuntime::load_reference_barrier_weak);
    }
  } else {
    assert(is_phantom, "only remaining strength");
    assert(!is_narrow, "phantom access cannot be narrow");
    target = CAST_FROM_FN_PTR(address, ShenandoahRuntime::load_reference_barrier_phantom);
  }
  // Calling with super_call_VM_leaf with c_rarg0/1 bypasses interpreter checks and avoids any moves.
  __ super_call_VM_leaf(target, c_rarg0, c_rarg1);
  __ pop_call_clobbered_registers_except(RegSet::of(V0));
  __ leave();

  __ bind(not_cset);

  __ move(result_dst, A0);
  if (result_dst == A0)
    __ pop2(R0, A1);
  else
    __ pop2(A0, A1);

  __ bind(heap_stable);
}

//
// Arguments:
//
// Inputs:
//   src:        oop location to load from, might be clobbered
//
// Output:
//   dst:        oop loaded from src location
//
// Kill:
//   SCR1 (scratch reg)
//
// Alias:
//   dst: SCR1 (might use SCR1 as temporary output register to avoid clobbering src)
//
void ShenandoahBarrierSetAssembler::load_at(MacroAssembler* masm, DecoratorSet decorators, BasicType type,
                                            Register dst, Address src, Register tmp1, Register tmp2) {
  // 1: non-reference load, no additional barrier is needed
  if (!is_reference_type(type)) {
    BarrierSetAssembler::load_at(masm, decorators, type, dst, src, tmp1, tmp2);
    return;
  }

  // 2: load a reference from src location and apply LRB if needed
  if (ShenandoahBarrierSet::need_load_reference_barrier(decorators, type)) {
    Register result_dst = dst;

    // Preserve src location for LRB
    if (dst == src.base() || dst == src.index() || dst == SCR1) {
      dst = SCR2;
    }
    assert_different_registers(dst, src.base(), src.index());

    BarrierSetAssembler::load_at(masm, decorators, type, dst, src, tmp1, tmp2);

    load_reference_barrier(masm, dst, src, decorators);

    if (dst != result_dst) {
      __ move(result_dst, dst);
      dst = result_dst;
    }
  } else {
    BarrierSetAssembler::load_at(masm, decorators, type, dst, src, tmp1, tmp2);
  }

  // 3: apply keep-alive barrier if needed
  if (ShenandoahBarrierSet::need_keep_alive_barrier(decorators, type)) {
    satb_barrier(masm /* masm */,
                 noreg /* obj */,
                 dst /* pre_val */,
                 TREG /* thread */,
                 tmp1 /* tmp1 */,
                 tmp2 /* tmp2 */);
  }
}

void ShenandoahBarrierSetAssembler::card_barrier(MacroAssembler* masm, Register obj, Register tmp) {
  assert(ShenandoahCardBarrier, "Should have been checked by caller");

  __ srli_d(obj, obj, CardTable::card_shift());

  assert(CardTable::dirty_card_val() == 0, "must be");

  Address curr_ct_holder_addr(TREG, in_bytes(ShenandoahThreadLocalData::card_table_offset()));
  __ ld_d(SCR1, curr_ct_holder_addr);
  __ add_d(SCR1, obj, SCR1);

  if (UseCondCardMark) {
    Label L_already_dirty;
    __ ld_bu(tmp, SCR1, 0);
    __ beqz(tmp, L_already_dirty);
    __ st_b(R0, SCR1, 0);
    __ bind(L_already_dirty);
  } else {
    __ st_b(R0, SCR1, 0);
  }
}

void ShenandoahBarrierSetAssembler::store_at(MacroAssembler* masm, DecoratorSet decorators, BasicType type,
                                             Address dst, Register val, Register tmp1, Register tmp2, Register tmp3) {
  // 1: non-reference types require no barriers
  if (!is_reference_type(type)) {
    BarrierSetAssembler::store_at(masm, decorators, type, dst, val, tmp1, tmp2, tmp3);
    return;
  }

  // Flatten object address right away for simplicity: likely needed by barriers
  if (dst.index() == noreg && dst.disp() == 0) {
    if (dst.base() != tmp3) {
      __ move(tmp3, dst.base());
    }
  } else {
    __ lea(tmp3, dst);
  }

  // 2: pre-barrier: SATB needs the previous value
  if (ShenandoahBarrierSet::need_satb_barrier(decorators, type)) {
    satb_barrier(masm,
                 tmp3 /* obj */,
                 tmp2 /* pre_val */,
                 TREG /* thread */,
                 tmp1 /* tmp */,
                 SCR1 /* tmp2 */);
  }

  // Store!
  BarrierSetAssembler::store_at(masm, decorators, type, Address(tmp3, 0), val, noreg, noreg, noreg);

  // 3: post-barrier: card barrier needs store address
  bool storing_non_null = (val != noreg);
  if (ShenandoahBarrierSet::need_card_barrier(decorators, type) && storing_non_null) {
    card_barrier(masm, tmp3, tmp1);
  }
}

void ShenandoahBarrierSetAssembler::try_resolve_jobject_in_native(MacroAssembler* masm, Register jni_env,
                                                                  Register obj, Register tmp, Label& slowpath) {
  Label done;
  // Resolve jobject
  BarrierSetAssembler::try_resolve_jobject_in_native(masm, jni_env, obj, tmp, slowpath);

  // Check for null.
  __ beqz(obj, done);

  assert(obj != SCR1, "need SCR1");
  Address gc_state(jni_env, ShenandoahThreadLocalData::gc_state_offset() - JavaThread::jni_environment_offset());
  __ lea(SCR1, gc_state);
  __ ld_b(SCR1, SCR1, 0);

  // Check for heap in evacuation phase
  __ andi(SCR1, SCR1, ShenandoahHeap::EVACUATION);
  __ bnez(SCR1, slowpath);

  __ bind(done);
}

void ShenandoahBarrierSetAssembler::try_peek_weak_handle_in_nmethod(MacroAssembler *masm, Register weak_handle,
                                                                    Register obj, Register tmp, Label& slow_path) {
  assert_different_registers(weak_handle, tmp, noreg);
  assert_different_registers(obj, tmp, noreg);


  Label done;

  // Peek weak handle using the standard implementation.
  BarrierSetAssembler::try_peek_weak_handle_in_nmethod(masm, weak_handle, obj, tmp, slow_path);

  // Check if the reference is null, and if it is, take the fast path.
  __ beqz(obj, done);

  Address gc_state(TREG, ShenandoahThreadLocalData::gc_state_offset());
  __ ld_bu(tmp, gc_state);

  // Check if the heap is under weak-reference/roots processing, in
  // which case we need to take the slow path.
  __ test_bit(tmp, tmp, ShenandoahHeap::WEAK_ROOTS_BITPOS);
  __ bnez(tmp, slow_path);
  __ bind(done);
}

void ShenandoahBarrierSetAssembler::check_oop(MacroAssembler* masm, Register obj, Register tmp1, Register tmp2, Label& L_error) {
  // Check if the oop is in the right area of memory
  __ li(tmp2, (intptr_t) Universe::verify_oop_mask());
  __ andr(tmp1, obj, tmp2);
  __ li(tmp2, (intptr_t) Universe::verify_oop_bits());

  // Compare tmp1 and tmp2.
  __ bne(tmp1, tmp2, L_error);

  // This routine is sometimes called before applying GC barriers.
  // With +COH, loading the klass may end up loading forwarding pointer instead.
  Label L_skip;
  if (UseCompactObjectHeaders) {
    Address gc_state(TREG, ShenandoahThreadLocalData::gc_state_offset());
    __ ld_bu(tmp1, gc_state);
    __ test_bit(tmp1, tmp1, ShenandoahHeap::HAS_FORWARDED_BITPOS);
    __ bnez(tmp1, L_skip);
  }

  // Make sure klass is 'reasonable', which is not zero.
  __ load_narrow_klass(tmp1, obj);
  __ beqz(tmp1, L_error);

  __ bind(L_skip);
}

void ShenandoahBarrierSetAssembler::gen_write_ref_array_post_barrier(MacroAssembler* masm, DecoratorSet decorators,
                                                                     Register start, Register count, Register tmp) {
  assert(ShenandoahCardBarrier, "Did you mean to enable ShenandoahCardBarrier?");

  Label L_loop, L_done;
  const Register end = count;

  // Zero count? Nothing to do.
  __ beqz(count, L_done);

  // end = start + count << LogBytesPerHeapOop
  // last element address to make inclusive
  __ alsl_d(end, count, start, LogBytesPerHeapOop-1);
  __ addi_d(end, end, -BytesPerHeapOop);
  __ srli_d(start, start, CardTable::card_shift());
  __ srli_d(end, end, CardTable::card_shift());

  // number of bytes to copy
  __ sub_d(count, end, start);

  Address curr_ct_holder_addr(TREG, in_bytes(ShenandoahThreadLocalData::card_table_offset()));
  __ ld_d(tmp, curr_ct_holder_addr);
  __ add_d(start, start, tmp);

  __ bind(L_loop);
  __ add_d(tmp, start, count);
  __ st_b(R0, tmp, 0);
  __ addi_d(count, count, -1);
  __ bge(count, R0, L_loop);
  __ bind(L_done);
}

#undef __

#ifdef COMPILER1

#define __ ce->masm()->

void ShenandoahBarrierSetAssembler::keepalive_barrier_c1_stub(LIR_Assembler* ce, ShenandoahKeepaliveBarrierStub* stub) {
  __ bind(*stub->entry());

  ShenandoahBarrierSetC1* bs = (ShenandoahBarrierSetC1*)BarrierSet::barrier_set()->barrier_set_c1();

  Register obj = stub->obj()->as_register();

  if (stub->do_load()) {
    ce->mem2reg(stub->addr(), stub->obj(), T_OBJECT, lir_patch_none, nullptr, false /* wide */);
  }
  __ beqz(obj, *stub->continuation());

  ce->store_parameter(obj, 0);
  __ call(bs->keepalive_barrier_stub(), relocInfo::runtime_call_type);
  __ b(*stub->continuation());
}

void ShenandoahBarrierSetAssembler::load_reference_barrier_c1_stub(LIR_Assembler* ce, ShenandoahLoadReferenceBarrierStub* stub) {
  __ bind(*stub->entry());

  ShenandoahBarrierSetC1* bs = (ShenandoahBarrierSetC1*) BarrierSet::barrier_set()->barrier_set_c1();

  Register obj = stub->obj()->as_register();
  Register addr = stub->addr()->as_pointer_register();
  Register slow_result = stub->slow_result()->as_register();
  assert_different_registers(obj, addr, slow_result);
  assert(slow_result == A0, "C1 must know about our slow call result register");

  ce->store_parameter(obj, 0);
  ce->store_parameter(addr, 1);
  __ call(bs->load_reference_barrier_stub(stub->decorators()), relocInfo::runtime_call_type);
  if (obj != slow_result) {
    __ move(obj, slow_result);
  }

  __ b(*stub->continuation());
}

#undef __

#define __ sasm->

void ShenandoahBarrierSetAssembler::keepalive_barrier_c1_runtime_stub(StubAssembler* sasm) {
  __ prologue("shenandoah_keepalive_barrier", false);
  const Register tmp_obj = A0;
  const Register tmp1 = A1;
  const Register tmp2 = A2;
  __ push(RegSet::of(tmp1, tmp2, tmp_obj));
  __ load_parameter(0, tmp_obj);
  satb_barrier(sasm, noreg, tmp_obj, TREG, tmp1, tmp2);
  __ pop(RegSet::of(tmp1, tmp2, tmp_obj));
  __ epilogue();
}

void ShenandoahBarrierSetAssembler::load_reference_barrier_c1_runtime_stub(StubAssembler* sasm, DecoratorSet decorators) {
  __ prologue("shenandoah_load_reference_barrier", false);
  const Register tmp_obj = A0;
  const Register tmp_addr = A1;
  __ push(RegSet::of(tmp_addr));
  __ load_parameter(0, tmp_obj);
  __ load_parameter(1, tmp_addr);
  load_reference_barrier(sasm, tmp_obj, Address(tmp_addr, 0), decorators);
  __ pop(RegSet::of(tmp_addr));
  __ epilogue();
}

#undef __

#endif // COMPILER1

#ifdef COMPILER2

#undef __
#define __ masm->

void ShenandoahBarrierSetAssembler::load_c2(const MachNode* node, MacroAssembler* masm, Register dst, Address src, Register tmp1, Register tmp2, bool is_narrow) {
  // Do the actual load. This load is the candidate for implicit null check, and MUST come first.
  if (is_narrow) {
    __ ld_wu(dst, src);
  } else {
    __ ld_d(dst, src);
  }

  ShenandoahBarrierStubC2::load_post(masm, node, dst, src, tmp1, tmp2, is_narrow);
}

void ShenandoahBarrierSetAssembler::store_c2(const MachNode* node, MacroAssembler* masm, Address dst, bool dst_narrow,
    Register src, bool src_narrow, Register tmp1, Register tmp2, Register tmp3, bool is_volatile) {

  ShenandoahBarrierStubC2::store_pre(masm, node, dst, tmp1, tmp2, tmp3, dst_narrow);

  // Do the actual store
  if (dst_narrow) {
    if (!src_narrow) {
      // Need to encode into tmp, because we cannot clobber src.
      assert(tmp1 != noreg, "need temp register");
      if ((node->barrier_data() & ShenandoahBitNotNull) == 0) {
        __ encode_heap_oop(tmp1, src);
      } else {
        __ encode_heap_oop_not_null(tmp1, src);
      }
      src = tmp1;
    }
    if (!is_volatile) {
      __ st_w(src, dst);
    } else {
      __ amswap_db_w(R0, src, dst.base());
    }
  } else {
    if (!is_volatile) {
      __ st_d(src, dst);
    } else {
      __ amswap_db_d(R0, src, dst.base());
    }
  }

  ShenandoahBarrierStubC2::store_post(masm, node, dst, tmp2, tmp3);
}

void ShenandoahBarrierSetAssembler::compare_and_set_c2(const MachNode* node, MacroAssembler* masm, Register res, Register addr,
    Register oldval, Register newval, Register tmp1, Register tmp2, Register tmp3, bool exchange, bool narrow, bool weak, bool is_acquire) {
  ShenandoahBarrierStubC2::load_store_pre(masm, node, Address(addr), tmp1, tmp2, tmp3, narrow);

  // CAS!
  if (narrow) {
    __ cmpxchg32(addr, oldval, newval, /* result */ res, /* sign */ false, /* retold */ false, is_acquire, weak, exchange);
  } else {
    __ cmpxchg(addr, oldval, newval, /* result */ res, /* retold */ false, is_acquire, weak, exchange);
  }

  ShenandoahBarrierStubC2::load_store_post(masm, node, Address(addr, 0), tmp2, tmp3);
}

void ShenandoahBarrierSetAssembler::get_and_set_c2(const MachNode* node, MacroAssembler* masm, Register preval,
    Register newval, Register addr, Register tmp1, Register tmp2, Register tmp3, bool is_acquire) {
  const bool is_narrow = node->bottom_type()->isa_narrowoop();

  ShenandoahBarrierStubC2::load_store_pre(masm, node, Address(addr, 0), tmp1, tmp2, tmp3, is_narrow);

  if (is_narrow) {
    if (is_acquire) {
      __ amswap_db_w(preval, newval, addr);
    } else {
      __ amswap_w(preval, newval, addr);
    }
    __ bstrpick_d(preval, preval, 31, 0);
  } else {
    if (is_acquire) {
      __ amswap_db_d(preval, newval, addr);
    } else {
      __ amswap_d(preval, newval, addr);
    }
  }

  ShenandoahBarrierStubC2::load_store_post(masm, node, Address(addr, 0), tmp2, tmp3);
}

#undef __
#define __ masm.

void ShenandoahBarrierStubC2::cardtable(MacroAssembler& masm, Address address, Register tmp1, Register tmp2) {
  assert(CardTable::dirty_card_val() == 0, "must be");
  Assembler::InlineSkippedInstructionsCounter skip_counter(&masm);

  // tmp1 = card table base (holder)
  Address curr_ct_holder_addr(TREG, in_bytes(ShenandoahThreadLocalData::card_table_offset()));
  __ ld_d(tmp1, curr_ct_holder_addr);

  // tmp1 = effective address
  __ lea(tmp2, address);

  // tmp2 = &card_table[ addr >> CardTable::card_shift() ] ; card index
  __ srli_d(tmp2, tmp2, CardTable::card_shift());
  __ add_d(tmp2, tmp2, tmp1);

  if (UseCondCardMark) {
    Label L_already_dirty;
    __ ld_bu(tmp1, Address(tmp2));
    __ beqz(tmp1, L_already_dirty);
    __ st_b(R0, Address(tmp2));
    __ bind(L_already_dirty);
  } else {
    __ st_b(R0, Address(tmp2));
  }
}

void ShenandoahBarrierStubC2::enter_if_gc_state(MacroAssembler& masm, const char test_state, Register tmp) {
  Assembler::InlineSkippedInstructionsCounter skip_counter(&masm);

  Address gc_state_fast(TREG, in_bytes(ShenandoahThreadLocalData::gc_state_fast_array_offset(test_state)));
  __ ld_bu(tmp, gc_state_fast);
  __ beqz(tmp, *continuation());
  __ b(*entry());

  // This is were the slowpath stub will return to or the code above will
  // jump to if the checks are false
  __ bind(*continuation());
}

void ShenandoahBarrierStubC2::emit_code(MacroAssembler& masm) {
  Assembler::InlineSkippedInstructionsCounter skip_counter(&masm);
  assert(_needs_keep_alive_barrier || _needs_load_ref_barrier, "Why are you here?");

  __ bind(*entry());

  // If we need to load ourselves, do it here.
  if (_do_load) {
    if (_narrow) {
      __ ld_wu(_obj, _addr);
    } else {
      __ ld_d(_obj, _addr);
    }
  }

  // If the object is null, there is no point in applying barriers.
  maybe_far_jump_if_zero(masm, _obj);

  // We need to make sure that loads done by callers survive across slow-path calls.
  // For self-loads, we need to care about the case when both KA and LRB are enabled (rare).
  bool needs_both_barriers = _needs_keep_alive_barrier && _needs_load_ref_barrier;
  if (!_do_load || needs_both_barriers) {
    preserve(_obj);
  }

  // Go for barriers. Barriers can return straight to continuation, as long
  // as another barrier is not needed and we can reach the fastpath.
  if (needs_both_barriers) {
    keepalive(masm, nullptr);
    lrb(masm);
  } else if (_needs_keep_alive_barrier) {
    keepalive(masm, continuation());
  } else if (_needs_load_ref_barrier) {
    lrb(masm);
  } else {
    ShouldNotReachHere();
  }
}

void ShenandoahBarrierStubC2::maybe_far_jump_if_zero(MacroAssembler& masm, Register reg) {
  Label L_short_jump;
  __ bnez(reg, L_short_jump);
  __ b(*continuation());
  __ bind(L_short_jump);
}

void ShenandoahBarrierStubC2::keepalive(MacroAssembler& masm, Label* L_done) {
  Address index(TREG, in_bytes(ShenandoahThreadLocalData::satb_mark_queue_index_offset()));
  Address buffer(TREG, in_bytes(ShenandoahThreadLocalData::satb_mark_queue_buffer_offset()));
  Label L_through, L_slowpath;

  // If another barrier is enabled as well, do a runtime check for a specific barrier.
  if (_needs_load_ref_barrier) {
    assert(L_done == nullptr, "L_done is always null when _needs_load_ref_barrier is true");
    Address gc_state_fast(TREG, in_bytes(ShenandoahThreadLocalData::gc_state_fast_array_offset(ShenandoahHeap::MARKING)));
    __ ld_bu(_tmp1, gc_state_fast);
    __ beqz(_tmp1, L_through);
  }

  // Fast-path: put object into buffer.
  // If buffer is already full, go slow.
  __ ld_d(_tmp1, index);
  __ beqz(_tmp1, L_slowpath);
  __ addi_d(_tmp1, _tmp1, -wordSize);
  __ st_d(_tmp1, index);
  __ ld_d(_tmp2, buffer);

  // Store the object in queue.
  // If object is narrow, we need to decode it before inserting.
  __ add_d(_tmp1, _tmp1, _tmp2);
  if (_narrow) {
    __ decode_heap_oop_not_null(_tmp2, _obj);
    __ st_d(_tmp2, Address(_tmp1));
  } else {
    __ st_d(_obj, Address(_tmp1));
  }

  // Fast-path exits here.
  if (L_done != nullptr) {
    __ b(*L_done);
  } else {
    __ b(L_through);
  }

  // Slow-path: call runtime to handle.
  __ bind(L_slowpath);

  {
    SaveLiveRegisters slr(&masm, this);

    // Go to runtime and handle the rest there.
    __ move(c_rarg0, _obj);
    __ call(keepalive_runtime_entry_addr(), relocInfo::runtime_call_type);
  }
  if (L_done != nullptr) {
    __ b(*L_done);
  } else {
    __ bind(L_through);
  }
}

void ShenandoahBarrierStubC2::lrb(MacroAssembler& masm) {
  Label L_slow;

  // If another barrier is enabled as well, do a runtime check for a specific barrier.
  if (_needs_keep_alive_barrier) {
    char state_to_check = ShenandoahHeap::HAS_FORWARDED | (_needs_load_ref_weak_barrier ? ShenandoahHeap::WEAK_ROOTS : 0);
    Address gc_state_fast(TREG, in_bytes(ShenandoahThreadLocalData::gc_state_fast_array_offset(state_to_check)));
    __ ld_bu(_tmp1, gc_state_fast);
    maybe_far_jump_if_zero(masm, _tmp1);
  }

  // If weak references are being processed, weak/phantom loads need to go slow,
  // regardless of their cset status.
  if (_needs_load_ref_weak_barrier) {
    Address gc_state_fast(TREG, in_bytes(ShenandoahThreadLocalData::gc_state_fast_array_offset(ShenandoahHeap::WEAK_ROOTS)));
    __ ld_bu(_tmp1, gc_state_fast);
    __ bnez(_tmp1, L_slow);
  }

  // Cset-check. Fall-through to slow if in collection set.
  if (_narrow) {
    __ decode_heap_oop_not_null(_tmp2, _obj);
  } else {
    __ move(_tmp2, _obj);
  }

  __ li(_tmp1, ShenandoahHeap::in_cset_fast_test_addr());
  __ srli_d(_tmp2, _tmp2, ShenandoahHeapRegion::region_size_bytes_shift_jint());
  __ add_d(_tmp1, _tmp1, _tmp2);
  __ ld_bu(_tmp1, Address(_tmp1, 0));
  maybe_far_jump_if_zero(masm, _tmp1);

  // Slow path
  __ bind(L_slow);

  // Obj is the result, need to temporarily stop preserving it.
  bool is_obj_preserved = is_preserved(_obj);
  if (is_obj_preserved) {
    dont_preserve(_obj);
  }
  {
    SaveLiveRegisters slr(&masm, this);

    // Shuffle in the arguments. The end result should be:
    //   c_rarg0 <- obj
    //   c_rarg1 <- lea(addr)
    if (c_rarg0 == _obj) {
      __ lea(c_rarg1, _addr);
    } else if (c_rarg1 == _obj) {
      __ move(_tmp1, c_rarg1);
      __ lea(c_rarg1, _addr);
      __ move(c_rarg0, _tmp1);
    } else {
      assert_different_registers(c_rarg1, _obj);
      __ lea(c_rarg1, _addr);
      __ move(c_rarg0, _obj);
    }

    // Go to runtime and handle the rest there.
    __ call(lrb_runtime_entry_addr(), relocInfo::runtime_call_type);

    // Save the result where needed. Narrow entries return narrowOop (32 bits)
    // we need to zero the upper 32 bits of A0.
    if (_narrow) {
      __ bstrpick_d(_obj, A0, 31, 0);
    } else {
      __ move(_obj, A0);
    }
  }
  if (is_obj_preserved) {
    preserve(_obj);
  }

  __ b(*continuation());
}

int ShenandoahBarrierStubC2::available_gp_registers() {
  Unimplemented(); // Not used
  return 0;
}

bool ShenandoahBarrierStubC2::is_special_register(Register r) {
  Unimplemented(); // Not used
  return true;
}

void ShenandoahBarrierStubC2::post_init() {
  // Do nothing.
}

#endif // COMPILER2
