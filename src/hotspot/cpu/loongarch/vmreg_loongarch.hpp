/*
 * Copyright (c) 2006, 2010, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2015, 2022, Loongson Technology. All rights reserved.
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

#ifndef CPU_LOONGARCH_VMREG_LOONGARCH_HPP
#define CPU_LOONGARCH_VMREG_LOONGARCH_HPP

inline bool is_Register() {
  return (unsigned int) value() < (unsigned int) ConcreteRegisterImpl::max_gpr;
}

inline Register as_Register() {
  assert( is_Register(), "must be");
  return ::as_Register(value() / Register::max_slots_per_register);
}

inline bool is_FloatRegister() {
  return value() >= ConcreteRegisterImpl::max_gpr && value() < ConcreteRegisterImpl::max_fpr;
}

inline FloatRegister as_FloatRegister() {
  assert( is_FloatRegister() && is_even(value()), "must be" );
  return ::as_FloatRegister((value() - ConcreteRegisterImpl::max_gpr) /
                            FloatRegister::max_slots_per_register);
}

inline   bool is_concrete() {
  assert(is_reg(), "must be");
  if (is_FloatRegister()) {
    int base = value() - ConcreteRegisterImpl::max_gpr;
    return base % FloatRegister::max_slots_per_register == 0;
  } else {
    return is_even(value());
  }
}

#endif // CPU_LOONGARCH_VMREG_LOONGARCH_HPP
