/*
 * Copyright (c) 2003, 2012, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2015, 2023, Loongson Technology. All rights reserved.
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

#ifndef CPU_LOONGARCH_TEMPLATETABLE_LOONGARCH_64_HPP
#define CPU_LOONGARCH_TEMPLATETABLE_LOONGARCH_64_HPP

  static void prepare_invoke(Register cache, Register recv);
  static void invokevirtual_helper(Register index, Register recv,
                                   Register flags);
  static void volatile_barrier();

  // Helpers
  static void index_check(Register array, Register index);
  static void index_check_without_pop(Register array, Register index);

#endif // CPU_LOONGARCH_TEMPLATETABLE_LOONGARCH_64_HPP
