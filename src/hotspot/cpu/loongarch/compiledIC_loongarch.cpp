/*
 * Copyright (c) 1997, 2014, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2015, 2024, Loongson Technology. All rights reserved.
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
#include "code/compiledIC.hpp"
#include "code/nmethod.hpp"
#include "logging/log.hpp"
#include "memory/resourceArea.hpp"
#include "runtime/mutexLocker.hpp"
#include "runtime/safepoint.hpp"

// ----------------------------------------------------------------------------

#define __ masm->
address CompiledDirectCall::emit_to_interp_stub(MacroAssembler *masm, address mark) {
  precond(__ code()->stubs()->start() != badAddress);
  precond(__ code()->stubs()->end() != badAddress);

  if (mark == nullptr) {
    mark = __ inst_mark();  // get mark within main instrs section.
  }

  address base = __ start_a_stub(CompiledDirectCall::to_interp_stub_size());
  if (base == nullptr)  return nullptr;  // CodeBuffer::expand failed
  // static stub relocation stores the instruction address of the call

  __ relocate(static_stub_Relocation::spec(mark), 0);

  {
    __ emit_static_call_stub();
  }

  // Update current stubs pointer and restore code_end.
  __ end_a_stub();
  return base;
}
#undef __

int CompiledDirectCall::to_interp_stub_size() {
  return NativeInstruction::nop_instruction_size + NativeMovConstReg::instruction_size + NativeGeneralJump::instruction_size;
}

int CompiledDirectCall::to_trampoline_stub_size() {
  return  NativeInstruction::nop_instruction_size + NativeCallTrampolineStub::instruction_size;
}

// Relocation entries for call stub, compiled java to interpreter.
int CompiledDirectCall::reloc_to_interp_stub() {
  return 16;
}

void CompiledDirectCall::set_to_interpreted(const methodHandle& callee, address entry) {
  address stub = find_stub();
  guarantee(stub != nullptr, "stub not found");

  // Creation also verifies the object.
  NativeMovConstReg* method_holder = nativeMovConstReg_at(stub + NativeInstruction::nop_instruction_size);
  NativeGeneralJump*        jump          = nativeGeneralJump_at(method_holder->next_instruction_address());
  verify_mt_safe(callee, entry, method_holder, jump);

  // Update stub.
  method_holder->set_data((intptr_t)callee());
  jump->set_jump_destination(entry);

  // Update jump to call.
  set_destination_mt_safe(stub);
}

void CompiledDirectCall::set_stub_to_clean(static_stub_Relocation* static_stub) {
  assert (CompiledIC_lock->is_locked() || SafepointSynchronize::is_at_safepoint(), "mt unsafe call");
  // Reset stub.
  address stub = static_stub->addr();
  assert(stub != nullptr, "stub not found");
  // Creation also verifies the object.
  NativeMovConstReg* method_holder = nativeMovConstReg_at(stub + NativeInstruction::nop_instruction_size);
  NativeGeneralJump* jump          = nativeGeneralJump_at(method_holder->next_instruction_address());
  method_holder->set_data(0);
  jump->set_jump_destination(jump->instruction_address());
}

//-----------------------------------------------------------------------------
// Non-product mode code
#ifndef PRODUCT

void CompiledDirectCall::verify() {
  // Verify call.
  _call->verify();
  if (os::is_MP()) {
    _call->verify_alignment();
  }

  // Verify stub.
  address stub = find_stub();
  assert(stub != nullptr, "no stub found for static call");
  // Creation also verifies the object.
  NativeMovConstReg* method_holder = nativeMovConstReg_at(stub + NativeInstruction::nop_instruction_size);
  NativeGeneralJump* jump          = nativeGeneralJump_at(method_holder->next_instruction_address());


  // Verify state.
  assert(is_clean() || is_call_to_compiled() || is_call_to_interpreted(), "sanity check");
}

#endif // !PRODUCT
