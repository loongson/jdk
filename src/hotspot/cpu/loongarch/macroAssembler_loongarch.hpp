/*
 * Copyright (c) 1997, 2013, Oracle and/or its affiliates. All rights reserved.
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

#ifndef CPU_LOONGARCH_MACROASSEMBLER_LOONGARCH_HPP
#define CPU_LOONGARCH_MACROASSEMBLER_LOONGARCH_HPP

#include "asm/assembler.hpp"
#include "code/vmreg.hpp"
#include "utilities/macros.hpp"

class OopMap;

#if INCLUDE_ZGC
const int ZBarrierRelocationFormatLoadBadMask = 0;
const int ZBarrierRelocationFormatMarkBadMask = 1;
const int ZBarrierRelocationFormatStoreGoodBits = 2;
const int ZBarrierRelocationFormatStoreBadMask = 3;
#endif

// MacroAssembler extends Assembler by frequently used macros.
//
// Instructions for which a 'better' code sequence exists depending
// on arguments should also go in here.

class MacroAssembler: public Assembler {
  friend class LIR_Assembler;
  friend class Runtime1;      // as_Address()

 public:
  // Compare code
  typedef enum {
    EQ = 0x01,
    NE = 0x02,
    GT = 0x03,
    GE = 0x04,
    LT = 0x05,
    LE = 0x06
  } CMCompare;

 public:
  // Support for VM calls
  //
  // This is the base routine called by the different versions of call_VM_leaf. The interpreter
  // may customize this version by overriding it for its purposes (e.g., to save/restore
  // additional registers when doing a VM call).
  #define VIRTUAL virtual

  VIRTUAL void call_VM_leaf_base(
    address entry_point,               // the entry point
    int     number_of_arguments        // the number of arguments to pop after the call
  );

 protected:
  // This is the base routine called by the different versions of call_VM. The interpreter
  // may customize this version by overriding it for its purposes (e.g., to save/restore
  // additional registers when doing a VM call).
  //
  // If no java_thread register is specified (noreg) than TREG will be used instead. call_VM_base
  // returns the register which contains the thread upon return. If a thread register has been
  // specified, the return value will correspond to that register. If no last_java_sp is specified
  // (noreg) than sp will be used instead.
  VIRTUAL void call_VM_base(           // returns the register containing the thread upon return
    Register oop_result,               // where an oop-result ends up if any; use noreg otherwise
    Register java_thread,              // the thread if computed before     ; use noreg otherwise
    Register last_java_sp,             // to set up last_Java_frame in stubs; use noreg otherwise
    address  entry_point,              // the entry point
    int      number_of_arguments,      // the number of arguments (w/o thread) to pop after the call
    bool     check_exceptions          // whether to check for pending exceptions after return
  );

  void call_VM_helper(Register oop_result, address entry_point, int number_of_arguments, bool check_exceptions = true);

  // helpers for FPU flag access
  // tmp is a temporary register, if none is available use noreg

 public:
  MacroAssembler(CodeBuffer* code) : Assembler(code) {}

  // These routines should emit JVMTI PopFrame and ForceEarlyReturn handling code.
  // The implementation is only non-empty for the InterpreterMacroAssembler,
  // as only the interpreter handles PopFrame and ForceEarlyReturn requests.
  virtual void check_and_handle_popframe(Register java_thread);
  virtual void check_and_handle_earlyret(Register java_thread);

  // Support for null-checks
  //
  // Generates code that causes a null OS exception if the content of reg is null.
  // If the accessed location is M[reg + offset] and the offset is known, provide the
  // offset. No explicit code generation is needed if the offset is within a certain
  // range (0 <= offset <= page_size).

  void null_check(Register reg, int offset = -1);
  static bool needs_explicit_null_check(intptr_t offset);
  static bool uses_implicit_null_check(void* address);

  // Required platform-specific helpers for Label::patch_instructions.
  // They _shadow_ the declarations in AbstractAssembler, which are undefined.
  static void pd_patch_instruction(address branch, address target, const char* file = nullptr, int line = 0);

  // Return whether code is emitted to a scratch blob.
  virtual bool in_scratch_emit_size() {
    return false;
  }

  address emit_trampoline_stub(int insts_call_instruction_offset, address target);

  void push_cont_fastpath(Register java_thread = TREG);
  void pop_cont_fastpath(Register java_thread = TREG);

  void inc_held_monitor_count(Register tmp);
  void dec_held_monitor_count(Register tmp);

  void flt_to_flt16(Register dst, FloatRegister src, FloatRegister tmp) {
    vfcvt_h_s(tmp, src, src);
    vpickve2gr_h(dst, tmp, 0);
  }

  void flt16_to_flt(FloatRegister dst, Register src, FloatRegister tmp) {
    vinsgr2vr_h(tmp, src, 0);
    vfcvtl_s_h(dst, tmp);
  }

  // Alignment
  void align(int modulus);
  void align(int modulus, int target);

  void post_call_nop();

  // Stack frame creation/removal
  void enter();
  void leave();

  // Frame creation and destruction shared between JITs.
  void build_frame(int framesize);
  void remove_frame(int framesize);

  // Support for getting the JavaThread pointer (i.e.; a reference to thread-local information)
  // The pointer will be loaded into the thread register.
  void get_thread(Register thread);

  // support for argument shuffling
  void simple_move32(VMRegPair src, VMRegPair dst, Register tmp = SCR1);
  void float_move(VMRegPair src, VMRegPair dst, Register tmp = SCR1);
  void long_move(VMRegPair src, VMRegPair dst, Register tmp = SCR1);
  void double_move(VMRegPair src, VMRegPair dst, Register tmp = SCR1);
  void object_move(
                   OopMap* map,
                   int oop_handle_offset,
                   int framesize_in_slots,
                   VMRegPair src,
                   VMRegPair dst,
                   bool is_receiver,
                   int* receiver_offset);

  // Support for VM calls
  //
  // It is imperative that all calls into the VM are handled via the call_VM macros.
  // They make sure that the stack linkage is setup correctly. call_VM's correspond
  // to ENTRY/ENTRY_X entry points while call_VM_leaf's correspond to LEAF entry points.


  void call_VM(Register oop_result,
               address entry_point,
               bool check_exceptions = true);
  void call_VM(Register oop_result,
               address entry_point,
               Register arg_1,
               bool check_exceptions = true);
  void call_VM(Register oop_result,
               address entry_point,
               Register arg_1, Register arg_2,
               bool check_exceptions = true);
  void call_VM(Register oop_result,
               address entry_point,
               Register arg_1, Register arg_2, Register arg_3,
               bool check_exceptions = true);

  // Overloadings with last_Java_sp
  void call_VM(Register oop_result,
               Register last_java_sp,
               address entry_point,
               int number_of_arguments = 0,
               bool check_exceptions = true);
  void call_VM(Register oop_result,
               Register last_java_sp,
               address entry_point,
               Register arg_1, bool
               check_exceptions = true);
  void call_VM(Register oop_result,
               Register last_java_sp,
               address entry_point,
               Register arg_1, Register arg_2,
               bool check_exceptions = true);
  void call_VM(Register oop_result,
               Register last_java_sp,
               address entry_point,
               Register arg_1, Register arg_2, Register arg_3,
               bool check_exceptions = true);

  void get_vm_result  (Register oop_result, Register thread);
  void get_vm_result_2(Register metadata_result, Register thread);
  void call_VM_leaf(address entry_point,
                    int number_of_arguments = 0);
  void call_VM_leaf(address entry_point,
                    Register arg_1);
  void call_VM_leaf(address entry_point,
                    Register arg_1, Register arg_2);
  void call_VM_leaf(address entry_point,
                    Register arg_1, Register arg_2, Register arg_3);

  // Super call_VM calls - correspond to MacroAssembler::call_VM(_leaf) calls
  void super_call_VM_leaf(address entry_point);
  void super_call_VM_leaf(address entry_point, Register arg_1);
  void super_call_VM_leaf(address entry_point, Register arg_1, Register arg_2);
  void super_call_VM_leaf(address entry_point, Register arg_1, Register arg_2, Register arg_3);

  // last Java Frame (fills frame anchor)
  void set_last_Java_frame(Register thread,
                           Register last_java_sp,
                           Register last_java_fp,
                           Label& last_java_pc);

  // thread in the default location (S6)
  void set_last_Java_frame(Register last_java_sp,
                           Register last_java_fp,
                           Label& last_java_pc);

  void set_last_Java_frame(Register last_java_sp,
                           Register last_java_fp,
                           Register last_java_pc);

  void reset_last_Java_frame(Register thread, bool clear_fp);

  // thread in the default location (S6)
  void reset_last_Java_frame(bool clear_fp);

  // jobjects
  void resolve_jobject(Register value, Register tmp1, Register tmp2);
  void resolve_global_jobject(Register value, Register tmp1, Register tmp2);

  // C 'boolean' to Java boolean: x == 0 ? 0 : 1
  void c2bool(Register x);

  void resolve_weak_handle(Register result, Register tmp1, Register tmp2);
  void resolve_oop_handle(Register result, Register tmp1, Register tmp2);
  void load_mirror(Register dst, Register method, Register tmp1, Register tmp2);

  void load_method_holder_cld(Register rresult, Register rmethod);
  void load_method_holder(Register holder, Register method);

  // oop manipulations
  void load_narrow_klass_compact(Register dst, Register src);
  void load_klass(Register dst, Register src);
  void store_klass(Register dst, Register src);
  void cmp_klass_compressed(Register oop, Register trial_klass, Register tmp, Label &L, bool equal);

  void access_load_at(BasicType type, DecoratorSet decorators, Register dst, Address src,
                      Register tmp1, Register tmp2);
  void access_store_at(BasicType type, DecoratorSet decorators, Address dst, Register val,
                       Register tmp1, Register tmp2, Register tmp3);

  void load_heap_oop(Register dst, Address src, Register tmp1,
                     Register tmp2, DecoratorSet decorators = 0);
  void load_heap_oop_not_null(Register dst, Address src, Register tmp1,
                              Register tmp2, DecoratorSet decorators = 0);
  void store_heap_oop(Address dst, Register val, Register tmp1,
                      Register tmp2, Register tmp3, DecoratorSet decorators = 0);

  // Used for storing null. All other oop constants should be
  // stored using routines that take a jobject.
  void store_heap_oop_null(Address dst);

  void store_klass_gap(Register dst, Register src);

  void encode_heap_oop(Register r);
  void encode_heap_oop(Register dst, Register src);
  void decode_heap_oop(Register r);
  void decode_heap_oop(Register dst, Register src);
  void encode_heap_oop_not_null(Register r);
  void decode_heap_oop_not_null(Register r);
  void encode_heap_oop_not_null(Register dst, Register src);
  void decode_heap_oop_not_null(Register dst, Register src);

  void encode_klass_not_null(Register r);
  void decode_klass_not_null(Register r);
  void encode_klass_not_null(Register dst, Register src);
  void decode_klass_not_null(Register dst, Register src);

  // if heap base register is used - reinit it with the correct value
  void reinit_heapbase();

  DEBUG_ONLY(void verify_heapbase(const char* msg);)

  void set_narrow_klass(Register dst, Klass* k);
  void set_narrow_oop(Register dst, jobject obj);

  // Sign extension
  void sign_extend_short(Register reg) { ext_w_h(reg, reg); }
  void sign_extend_byte(Register reg)  { ext_w_b(reg, reg); }

  // java.lang.Math::round intrinsics
  void java_round_float(Register dst, FloatRegister src,
                        FloatRegister vtemp1);
  void java_round_float_lsx(FloatRegister dst, FloatRegister src,
                            FloatRegister vtemp1, FloatRegister vtemp2);
  void java_round_float_lasx(FloatRegister dst, FloatRegister src,
                             FloatRegister vtemp1, FloatRegister vtemp2);
  void java_round_double(Register dst, FloatRegister src,
                         FloatRegister vtemp1);
  void java_round_double_lsx(FloatRegister dst, FloatRegister src,
                             FloatRegister vtemp1, FloatRegister vtemp2);
  void java_round_double_lasx(FloatRegister dst, FloatRegister src,
                              FloatRegister vtemp1, FloatRegister vtemp2);

  // allocation
  void tlab_allocate(
    Register obj,                      // result: pointer to object after successful allocation
    Register var_size_in_bytes,        // object size in bytes if unknown at compile time; invalid otherwise
    int      con_size_in_bytes,        // object size in bytes if   known at compile time
    Register t1,                       // temp register
    Register t2,                       // temp register
    Label&   slow_case                 // continuation point if fast allocation fails
  );
  // interface method calling
  void lookup_interface_method(Register recv_klass,
                               Register intf_klass,
                               RegisterOrConstant itable_index,
                               Register method_result,
                               Register scan_temp,
                               Label& no_such_interface,
                               bool return_method = true);

  // virtual method calling
  void lookup_virtual_method(Register recv_klass,
                             RegisterOrConstant vtable_index,
                             Register method_result);

  // Test sub_klass against super_klass, with fast and slow paths.

  // The fast path produces a tri-state answer: yes / no / maybe-slow.
  // One of the three labels can be null, meaning take the fall-through.
  // If super_check_offset is -1, the value is loaded up from super_klass.
  // No registers are killed, except temp_reg.
  void check_klass_subtype_fast_path(Register sub_klass,
                                     Register super_klass,
                                     Register temp_reg,
                                     Label* L_success,
                                     Label* L_failure,
                                     Label* L_slow_path,
                RegisterOrConstant super_check_offset = RegisterOrConstant(-1));

  // The rest of the type check; must be wired to a corresponding fast path.
  // It does not repeat the fast path logic, so don't use it standalone.
  // The temp_reg and temp2_reg can be noreg, if no temps are available.
  // Updates the sub's secondary super cache as necessary.
  // If set_cond_codes, condition codes will be Z on success, NZ on failure.
  template <bool LONG_JMP>
  void check_klass_subtype_slow_path(Register sub_klass,
                                     Register super_klass,
                                     Register temp_reg,
                                     Register temp2_reg,
                                     Label* L_success,
                                     Label* L_failure,
                                     bool set_cond_codes = false);

  // Simplified, combined version, good for typical uses.
  // Falls through on failure.
  void check_klass_subtype(Register sub_klass,
                           Register super_klass,
                           Register temp_reg,
                           Label& L_success);

  // As above, but with a constant super_klass.
  // The result is in Register result, not the condition codes.
  bool lookup_secondary_supers_table(Register r_sub_klass,
                                     Register r_super_klass,
                                     Register result,
                                     Register tmp1,
                                     Register tmp2,
                                     Register tmp3,
                                     Register tmp4,
                                     u1 super_klass_slot,
                                     bool stub_is_near = false);

  void verify_secondary_supers_table(Register r_sub_klass,
                                     Register r_super_klass,
                                     Register result,
                                     Register tmp1,
                                     Register tmp2,
                                     Register tmp3);

  void lookup_secondary_supers_table_slow_path(Register r_super_klass,
                                               Register r_array_base,
                                               Register r_array_index,
                                               Register r_bitmap,
                                               Register result,
                                               Register tmp1);

  void clinit_barrier(Register klass,
                      Register scratch,
                      Label* L_fast_path = nullptr,
                      Label* L_slow_path = nullptr);


  // Debugging

  // only if +VerifyOops
  void _verify_oop(Register reg, const char* s, const char* file, int line);
  void _verify_oop_addr(Address addr, const char* s, const char* file, int line);

  void _verify_oop_checked(Register reg, const char* s, const char* file, int line) {
    if (VerifyOops) {
      _verify_oop(reg, s, file, line);
    }
  }
  void _verify_oop_addr_checked(Address reg, const char* s, const char* file, int line) {
    if (VerifyOops) {
      _verify_oop_addr(reg, s, file, line);
    }
  }

  void verify_oop_subroutine();

  // TODO: verify method and klass metadata (compare against vptr?)
  void _verify_method_ptr(Register reg, const char * msg, const char * file, int line) {}
  void _verify_klass_ptr(Register reg, const char * msg, const char * file, int line){}

#define verify_oop(reg) _verify_oop_checked(reg, "broken oop " #reg, __FILE__, __LINE__)
#define verify_oop_msg(reg, msg) _verify_oop_checked(reg, "broken oop " #reg ", " #msg, __FILE__, __LINE__)
#define verify_oop_addr(addr) _verify_oop_addr_checked(addr, "broken oop addr " #addr, __FILE__, __LINE__)
#define verify_method_ptr(reg) _verify_method_ptr(reg, "broken method " #reg, __FILE__, __LINE__)
#define verify_klass_ptr(reg) _verify_method_ptr(reg, "broken klass " #reg, __FILE__, __LINE__)

  // prints msg, dumps registers and stops execution
  void stop(const char* msg);

  static void debug(char* msg/*, RegistersForDebugging* regs*/);
  static void debug64(char* msg, int64_t pc, int64_t regs[]);

  void untested()                                { stop("untested"); }

  void unimplemented(const char* what = "");

  void should_not_reach_here()                   { stop("should not reach here"); }

  // Stack overflow checking
  void bang_stack_with_offset(int offset) {
    // stack grows down, caller passes positive offset
    assert(offset > 0, "must bang with negative offset");
    if (offset <= 2048) {
      st_w(A0, SP, -offset);
    } else if (offset <= 32768 && !(offset & 3)) {
      stptr_w(A0, SP, -offset);
    } else {
      li(AT, offset);
      sub_d(AT, SP, AT);
      st_w(A0, AT, 0);
    }
  }

  // Writes to stack successive pages until offset reached to check for
  // stack overflow + shadow pages.  Also, clobbers tmp
  void bang_stack_size(Register size, Register tmp);

  // Check for reserved stack access in method being exited (for JIT)
  void reserved_stack_check();

  void safepoint_poll(Label& slow_path, Register thread_reg, bool at_return, bool acquire, bool in_nmethod);

  void verify_tlab(Register t1, Register t2);

  // the follow two might use AT register, be sure you have no meanful data in AT before you call them
  void increment(Register reg, int imm);
  void decrement(Register reg, int imm);
  void increment(Address addr, int imm = 1);
  void decrement(Address addr, int imm = 1);

  // Helper functions for statistics gathering.
  void atomic_inc32(address counter_addr, int inc, Register tmp_reg1, Register tmp_reg2);

  // Calls
  void call(address entry);
  void call(address entry, relocInfo::relocType rtype);
  void call(address entry, RelocationHolder& rh);
  void call_long(address entry);

  // Return: the call PC or null if CodeCache is full.
  address trampoline_call(AddressLiteral entry);

  static const unsigned long branch_range = NOT_DEBUG(128 * M) DEBUG_ONLY(2 * M);

  static bool far_branches() {
    if (ForceUnreachable) {
      return true;
    } else {
      return ReservedCodeCacheSize > branch_range;
    }
  }

  // Emit the CompiledIC call idiom
  address ic_call(address entry, jint method_index = 0);
  static int ic_check_size();
  int ic_check(int end_alignment);

  void emit_static_call_stub();

  // Jumps
  void jmp(address entry);
  void jmp(address entry, relocInfo::relocType rtype);
  void jmp_far(Label& L); // patchable

  /* branches may exceed 16-bit offset */
  void b_far(address entry);
  void b_far(Label& L);

  void bne_far    (Register rs, Register rt, address entry);
  void bne_far    (Register rs, Register rt, Label& L);

  void beq_far    (Register rs, Register rt, address entry);
  void beq_far    (Register rs, Register rt, Label& L);

  void blt_far    (Register rs, Register rt, address entry, bool is_signed);
  void blt_far    (Register rs, Register rt, Label& L, bool is_signed);

  void bge_far    (Register rs, Register rt, address entry, bool is_signed);
  void bge_far    (Register rs, Register rt, Label& L, bool is_signed);

  static bool patchable_branches() {
    const unsigned long branch_range = NOT_DEBUG(128 * M) DEBUG_ONLY(2 * M);
    return ReservedCodeCacheSize > branch_range;
  }

  static bool reachable_from_branch_short(jlong offs);

  void patchable_jump_far(Register ra, jlong offs);
  void patchable_jump(address target, bool force_patchable = false);
  void patchable_call(address target, address call_size = 0);

  // Floating
  void generate_dsin_dcos(bool isCos, address npio2_hw, address two_over_pi,
                          address pio2, address dsin_coef, address dcos_coef);

  // Data

  // Load and store values by size and signed-ness
  void load_sized_value(Register dst, Address src, size_t size_in_bytes, bool is_signed, Register dst2 = noreg);
  void store_sized_value(Address dst, Register src, size_t size_in_bytes, Register src2 = noreg);

  // swap the two byte of the low 16-bit halfword
  void bswap_h(Register dst, Register src);
  void bswap_hu(Register dst, Register src);

  // convert big endian integer to little endian integer
  void bswap_w(Register dst, Register src);

  // test single bit in src, result is set to dst
  void test_bit(Register dst, Register src, uint32_t bit_pos);

  void cmpxchg(Address addr, Register oldval, Register newval, Register resflag,
               bool retold, bool acquire, bool weak = false, bool exchange = false);
  void cmpxchg(Address addr, Register oldval, Register newval, Register tmp,
               bool retold, bool acquire, Label& succ, Label* fail = nullptr);
  void cmpxchg32(Address addr, Register oldval, Register newval, Register resflag,
                 bool sign, bool retold, bool acquire, bool weak = false, bool exchange = false);
  void cmpxchg32(Address addr, Register oldval, Register newval, Register tmp,
                 bool sign, bool retold, bool acquire, Label& succ, Label* fail = nullptr);
  void cmpxchg16(Address addr, Register oldval, Register newval, Register resflag,
                 bool sign, bool retold, bool acquire, bool weak = false, bool exchange = false);
  void cmpxchg16(Address addr, Register oldval, Register newval, Register tmp,
                 bool sign, bool retold, bool acquire, Label& succ, Label* fail = nullptr);
  void cmpxchg8(Address addr, Register oldval, Register newval, Register resflag,
                 bool sign, bool retold, bool acquire, bool weak = false, bool exchange = false);
  void cmpxchg8(Address addr, Register oldval, Register newval, Register tmp,
                 bool sign, bool retold, bool acquire, Label& succ, Label* fail = nullptr);

  void push (Register reg)      { addi_d(SP, SP, -8); st_d  (reg, SP, 0); }
  void push (FloatRegister reg) { addi_d(SP, SP, -8); fst_d (reg, SP, 0); }
  void pop  (Register reg)      { ld_d  (reg, SP, 0);  addi_d(SP, SP, 8); }
  void pop  (FloatRegister reg) { fld_d (reg, SP, 0);  addi_d(SP, SP, 8); }
  void pop  ()                  { addi_d(SP, SP, 8); }
  void pop2 ()                  { addi_d(SP, SP, 16); }
  void push2(Register reg1, Register reg2);
  void pop2 (Register reg1, Register reg2);
  // Push and pop everything that might be clobbered by a native
  // runtime call except SCR1 and SCR2.  (They are always scratch,
  // so we don't have to protect them.)  Only save the lower 64 bits
  // of each vector register. Additional registers can be excluded
  // in a passed RegSet.
  void push_call_clobbered_registers_except(RegSet exclude);
  void pop_call_clobbered_registers_except(RegSet exclude);

  void push_call_clobbered_registers() {
    push_call_clobbered_registers_except(RegSet());
  }
  void pop_call_clobbered_registers() {
    pop_call_clobbered_registers_except(RegSet());
  }
  void push(RegSet regs) { if (regs.bits()) push(regs.bits()); }
  void pop(RegSet regs) { if (regs.bits()) pop(regs.bits()); }
  void push_fpu(FloatRegSet regs) { if (regs.bits()) push_fpu(regs.bits()); }
  void pop_fpu(FloatRegSet regs) { if (regs.bits()) pop_fpu(regs.bits()); }
  void push_vp(FloatRegSet regs) { if (regs.bits()) push_vp(regs.bits()); }
  void pop_vp(FloatRegSet regs) { if (regs.bits()) pop_vp(regs.bits()); }

  void li(Register rd, jlong value);
  void li(Register rd, address addr) { li(rd, (long)addr); }
  void patchable_li52(Register rd, jlong value);
  void lipc(Register rd, Label& L);

  void move(Register rd, Register rs)   { orr(rd, rs, R0); }
  void move_u32(Register rd, Register rs)   { add_w(rd, rs, R0); }
  void mov_metadata(Register dst, Metadata* obj);
  void mov_metadata(Address dst, Metadata* obj);

  // Load the base of the cardtable byte map into reg.
  void load_byte_map_base(Register reg);

  // method handles (JSR 292)
  Address argument_address(RegisterOrConstant arg_slot, int extra_slot_offset = 0);


  // LA added:
  void jr  (Register reg)        { jirl(R0, reg, 0); }
  void jalr(Register reg)        { jirl(RA, reg, 0); }
  void nop ()                    { andi(R0, R0, 0); }
  void andr(Register rd, Register rj, Register rk) { AND(rd, rj, rk); }
  void xorr(Register rd, Register rj, Register rk) { XOR(rd, rj, rk); }
  void orr (Register rd, Register rj, Register rk) {  OR(rd, rj, rk); }
  void lea (Register rd, Address src);
  void lea(Register dst, AddressLiteral adr);
  void lea_long(Register dst, AddressLiteral adr);
  static int  patched_branch(int dest_pos, int inst, int inst_pos);

  // Conditional move
  void cmp_cmov_zero(Register        op1,
                Register        op2,
                Register        dst,
                Register        src,
                CMCompare       cmp = EQ,
                bool      is_signed = true);
  void cmp_cmov(Register        op1,
                Register        op2,
                Register        dst,
                Register        src1,
                Register        src2,
                CMCompare       cmp = EQ,
                bool      is_signed = true);
  void cmp_cmov(Register        op1,
                Register        op2,
                Register        dst,
                Register        src,
                CMCompare       cmp = EQ,
                bool      is_signed = true);
  void cmp_cmov(FloatRegister   op1,
                FloatRegister   op2,
                Register        dst,
                Register        src,
                FloatRegister   tmp1,
                FloatRegister   tmp2,
                CMCompare       cmp = EQ,
                bool       is_float = true);
  void cmp_cmov(FloatRegister   op1,
                FloatRegister   op2,
                FloatRegister   dst,
                FloatRegister   src,
                CMCompare       cmp = EQ,
                bool       is_float = true);
  void cmp_cmov(Register        op1,
                Register        op2,
                FloatRegister   dst,
                FloatRegister   src,
                CMCompare       cmp = EQ,
                bool      is_signed = true);

  void membar(Membar_mask_bits hint);

  void bind(Label& L) {
    Assembler::bind(L);
    code()->clear_last_insn();
  }

  // ChaCha20 functions support block
  void cc20_quarter_round(FloatRegister aVec, FloatRegister bVec,
                          FloatRegister cVec, FloatRegister dVec);
  void cc20_shift_lane_org(FloatRegister bVec, FloatRegister cVec,
                           FloatRegister dVec, bool colToDiag);

  // CRC32 code for java.util.zip.CRC32::update() intrinsic.
  void update_byte_crc32(Register crc, Register val, Register table);

  // CRC32 code for java.util.zip.CRC32::updateBytes() intrinsic.
  void kernel_crc32(Register crc, Register buf, Register len, Register tmp);

  // CRC32C code for java.util.zip.CRC32C::updateBytes() intrinsic.
  void kernel_crc32c(Register crc, Register buf, Register len, Register tmp);

  // Code for java.lang.StringCoding::countPositives intrinsic.
  void count_positives(Register src, Register len, Register result,
                       Register tmp1, Register tmp2);

  // Code for java.lang.StringUTF16::compress intrinsic.
  void char_array_compress(Register src, Register dst,
                           Register len, Register result,
                           Register tmp1, Register tmp2, Register tmp3,
                           FloatRegister vtemp1, FloatRegister vtemp2,
                           FloatRegister vtemp3, FloatRegister vtemp4);

  // Code for java.lang.StringLatin1::inflate intrinsic.
  void byte_array_inflate(Register src, Register dst, Register len,
                          Register tmp1, Register tmp2,
                          FloatRegister vtemp1, FloatRegister vtemp2);

  // Encode UTF16 to ISO_8859_1 or ASCII.
  // Return len on success or position of first mismatch.
  void encode_iso_array(Register src, Register dst,
                        Register len, Register result,
                        Register tmp1, Register tmp2,
                        Register tmp3, bool ascii,
                        FloatRegister vtemp1, FloatRegister vtemp2,
                        FloatRegister vtemp3, FloatRegister vtemp4);

  // Code for java.math.BigInteger::mulAdd intrinsic.
  void mul_add(Register out, Register in, Register offset,
               Register len, Register k);
  void cad(Register dst, Register src1, Register src2, Register carry);
  void cadc(Register dst, Register src1, Register src2, Register carry);
  void adc(Register dst, Register src1, Register src2, Register carry);
  void wide_mul(Register prod_lo, Register prod_hi, Register n, Register m);
  void wide_madd(Register sum_lo, Register sum_hi, Register n,
                Register m, Register tmp1, Register tmp2);

  void movoop(Register dst, jobject obj);

  // Helpers for the array_fill() macro
  inline void tiny_fill_0_24(Register to, Register value);

  // Inner part of the generate_fill() stub
  inline void array_fill(BasicType t, Register to,
                         Register value, Register count, bool aligned);
  inline void array_fill_lsx(BasicType t, Register to,
                             Register value, Register count);
  inline void array_fill_lasx(BasicType t, Register to,
                              Register value, Register count);

#undef VIRTUAL

  void cast_primitive_type(BasicType type, Register reg) {
    switch (type) {
      case T_BOOLEAN: c2bool(reg);                 break;
      case T_CHAR   : bstrpick_d(reg, reg, 15, 0); break;
      case T_BYTE   : sign_extend_byte (reg);      break;
      case T_SHORT  : sign_extend_short(reg);      break;
      case T_INT    : add_w(reg, reg, R0);         break;
      case T_LONG   : /* nothing to do */          break;
      case T_VOID   : /* nothing to do */          break;
      case T_FLOAT  : /* nothing to do */          break;
      case T_DOUBLE : /* nothing to do */          break;
      default: ShouldNotReachHere();
    }
  }

  void lightweight_lock(Register basic_lock, Register obj, Register tmp1, Register tmp2, Register tmp3, Label& slow);
  void lightweight_unlock(Register obj, Register tmp1, Register tmp2, Register tmp3, Label& slow);

#if INCLUDE_ZGC
  void patchable_li16(Register rd, uint16_t value);
  void z_color(Register dst, Register src, Register tmp);
  void z_uncolor(Register ref);
  void check_color(Register ref, Register tmp, bool on_non_strong);
#endif

private:
  void push(unsigned int bitset);
  void pop(unsigned int bitset);
  void push_fpu(unsigned int bitset);
  void pop_fpu(unsigned int bitset);
  void push_vp(unsigned int bitset);
  void pop_vp(unsigned int bitset);

  // Check the current thread doesn't need a cross modify fence.
  void verify_cross_modify_fence_not_required() PRODUCT_RETURN;
  void generate_kernel_sin(FloatRegister x, bool iyIsOne, address dsin_coef);
  void generate_kernel_cos(FloatRegister x, address dcos_coef);
  void generate__ieee754_rem_pio2(address npio2_hw, address two_over_pi, address pio2);
  void generate__kernel_rem_pio2(address two_over_pi, address pio2);

  void repne_scan(Register addr, Register value, Register count, Register tmp);
};

#ifdef ASSERT
inline bool AbstractAssembler::pd_check_instruction_mark() { return true; }
#endif

struct tableswitch {
  Register _reg;
  int _insn_index; jint _first_key; jint _last_key;
  Label _after;
  Label _branches;
};

#endif // CPU_LOONGARCH_MACROASSEMBLER_LOONGARCH_HPP
