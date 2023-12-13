/*
 * Copyright (c) 1999, 2013, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2023, Loongson Technology. All rights reserved.
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

#ifndef __AMCAS_ASM_H__
#define __AMCAS_ASM_H__
   asm(
      ".macro   parse_r var r \n\t"
      "\\var    = -1          \n\t"
      ".ifc     \\r, $r0      \n\t"
      "\\var    = 0           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r1      \n\t"
      "\\var    = 1           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r2      \n\t"
      "\\var    = 2           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r3      \n\t"
      "\\var    = 3           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r4      \n\t"
      "\\var    = 4           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r5      \n\t"
      "\\var    = 5           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r6      \n\t"
      "\\var    = 6           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r7      \n\t"
      "\\var    = 7           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r8      \n\t"
      "\\var    = 8           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r9      \n\t"
      "\\var    = 9           \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r10     \n\t"
      "\\var    = 10          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r11     \n\t"
      "\\var    = 11          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r12     \n\t"
      "\\var    = 12          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r13     \n\t"
      "\\var    = 13          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r14     \n\t"
      "\\var    = 14          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r15     \n\t"
      "\\var    = 15          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r16     \n\t"
      "\\var    = 16          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r17     \n\t"
      "\\var    = 17          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r18     \n\t"
      "\\var    = 18          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r19     \n\t"
      "\\var    = 19          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r20     \n\t"
      "\\var    = 20          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r21     \n\t"
      "\\var    = 21          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r22     \n\t"
      "\\var    = 22          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r23     \n\t"
      "\\var    = 23          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r24     \n\t"
      "\\var    = 24          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r25     \n\t"
      "\\var    = 25          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r26     \n\t"
      "\\var    = 26          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r27     \n\t"
      "\\var    = 27          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r28     \n\t"
      "\\var    = 28          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r29     \n\t"
      "\\var    = 29          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r30     \n\t"
      "\\var    = 30          \n\t"
      ".endif                 \n\t"
      ".ifc     \\r, $r31     \n\t"
      "\\var    = 31          \n\t"
      ".endif                 \n\t"
      ".iflt    \\var         \n\t"
      ".error                 \n\t"
      ".endif                 \n\t"
      ".endm                  \n\t"

      ".macro amcas_w rd, rk, rj                                     \n\t"
      "parse_r d, \\rd                                                \n\t"
      "parse_r j, \\rj                                                \n\t"
      "parse_r k, \\rk                                                \n\t"
      ".word ((0b00111000010110010 << 15) | (k << 10) | (j << 5) | d) \n\t"
      ".endm                                                          \n\t"

      ".macro amcas_d rd, rk, rj                                     \n\t"
      "parse_r d, \\rd                                                \n\t"
      "parse_r j, \\rj                                                \n\t"
      "parse_r k, \\rk                                                \n\t"
      ".word ((0b00111000010110011 << 15) | (k << 10) | (j << 5) | d) \n\t"
      ".endm                                                          \n\t"

      ".macro amcas_db_b rd, rk, rj                                   \n\t"
      "parse_r d, \\rd                                                \n\t"
      "parse_r j, \\rj                                                \n\t"
      "parse_r k, \\rk                                                \n\t"
      ".word ((0b00111000010110100 << 15) | (k << 10) | (j << 5) | d) \n\t"
      ".endm                                                          \n\t"

      ".macro amcas_db_w rd, rk, rj                                   \n\t"
      "parse_r d, \\rd                                                \n\t"
      "parse_r j, \\rj                                                \n\t"
      "parse_r k, \\rk                                                \n\t"
      ".word ((0b00111000010110110 << 15) | (k << 10) | (j << 5) | d) \n\t"
      ".endm                                                          \n\t"

      ".macro amcas_db_d rd, rk, rj                                   \n\t"
      "parse_r d, \\rd                                                \n\t"
      "parse_r j, \\rj                                                \n\t"
      "parse_r k, \\rk                                                \n\t"
      ".word ((0b00111000010110111 << 15) | (k << 10) | (j << 5) | d) \n\t"
      ".endm                                                          \n\t"
  );
#endif /* __AMCAS_ASM_H__ */
