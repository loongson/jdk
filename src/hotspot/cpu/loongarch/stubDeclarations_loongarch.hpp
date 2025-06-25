/*
 * Copyright (c) 2025, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2025, Loongson Technology. All rights reserved.
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

#ifndef CPU_LOONGARCH_STUBDECLARATIONS_HPP
#define CPU_LOONGARCH_STUBDECLARATIONS_HPP

#define STUBGEN_PREUNIVERSE_BLOBS_ARCH_DO(do_stub,                      \
                                          do_arch_blob,                 \
                                          do_arch_entry,                \
                                          do_arch_entry_init)           \
  do_arch_blob(preuniverse, 0)                                          \


#define STUBGEN_INITIAL_BLOBS_ARCH_DO(do_stub,                          \
                                      do_arch_blob,                     \
                                      do_arch_entry,                    \
                                      do_arch_entry_init)               \
  do_arch_blob(initial, 20000)                                          \


#define STUBGEN_CONTINUATION_BLOBS_ARCH_DO(do_stub,                     \
                                           do_arch_blob,                \
                                           do_arch_entry,               \
                                           do_arch_entry_init)          \
  do_arch_blob(continuation, 2000)                                      \


#define STUBGEN_COMPILER_BLOBS_ARCH_DO(do_stub,                         \
                                       do_arch_blob,                    \
                                       do_arch_entry,                   \
                                       do_arch_entry_init)              \
  do_arch_blob(compiler, 70000)                                         \
  do_stub(compiler, vector_iota_indices)                                \
  do_arch_entry(la, compiler, vector_iota_indices,                      \
                vector_iota_indices, vector_iota_indices)               \
  do_stub(compiler, string_indexof_linear_ll)                           \
  do_arch_entry(la, compiler, string_indexof_linear_ll,                 \
                string_indexof_linear_ll, string_indexof_linear_ll)     \
  do_stub(compiler, string_indexof_linear_uu)                           \
  do_arch_entry(la, compiler, string_indexof_linear_uu,                 \
                string_indexof_linear_uu, string_indexof_linear_uu)     \
  do_stub(compiler, string_indexof_linear_ul)                           \
  do_arch_entry(la, compiler, string_indexof_linear_ul,                 \
                string_indexof_linear_ul, string_indexof_linear_ul)     \


#define STUBGEN_FINAL_BLOBS_ARCH_DO(do_stub,                            \
                                    do_arch_blob,                       \
                                    do_arch_entry,                      \
                                    do_arch_entry_init)                 \
  do_arch_blob(final, 60000 ZGC_ONLY(+477000))                          \
  do_stub(final, jlong_fill)                                            \
  do_arch_entry(la, final, jlong_fill,                                  \
                jlong_fill, jlong_fill)                                 \
  do_stub(final, arrayof_jlong_fill)                                    \
  do_arch_entry(la, final, arrayof_jlong_fill,                          \
                arrayof_jlong_fill, arrayof_jlong_fill)                 \
  do_stub(final, disjoint_large_copy_lasx)                              \
  do_arch_entry(la, final, disjoint_large_copy_lasx,                    \
                disjoint_large_copy_lasx, disjoint_large_copy_lasx)     \
  do_stub(final, disjoint_large_copy_oop_lasx)                          \
  do_arch_entry(la, final, disjoint_large_copy_oop_lasx,                \
                disjoint_large_copy_oop_lasx,                           \
                disjoint_large_copy_oop_lasx)                           \
  do_stub(final, disjoint_large_copy_oop_uninit_lasx)                   \
  do_arch_entry(la, final, disjoint_large_copy_oop_uninit_lasx,         \
                disjoint_large_copy_oop_uninit_lasx,                    \
                disjoint_large_copy_oop_uninit_lasx)                    \
  do_stub(final, conjoint_large_copy_lasx)                              \
  do_arch_entry(la, final, conjoint_large_copy_lasx,                    \
                conjoint_large_copy_lasx, conjoint_large_copy_lasx)     \
  do_stub(final, conjoint_large_copy_oop_lasx)                          \
  do_arch_entry(la, final, conjoint_large_copy_oop_lasx,                \
                conjoint_large_copy_oop_lasx,                           \
                conjoint_large_copy_oop_lasx)                           \
  do_stub(final, conjoint_large_copy_oop_uninit_lasx)                   \
  do_arch_entry(la, final, conjoint_large_copy_oop_uninit_lasx,         \
                conjoint_large_copy_oop_uninit_lasx,                    \
                conjoint_large_copy_oop_uninit_lasx)                    \
  do_stub(final, disjoint_large_copy_lsx)                               \
  do_arch_entry(la, final, disjoint_large_copy_lsx,                     \
                disjoint_large_copy_lsx, disjoint_large_copy_lsx)       \
  do_stub(final, disjoint_large_copy_oop_lsx)                           \
  do_arch_entry(la, final, disjoint_large_copy_oop_lsx,                 \
                disjoint_large_copy_oop_lsx,                            \
                disjoint_large_copy_oop_lsx)                            \
  do_stub(final, disjoint_large_copy_oop_uninit_lsx)                    \
  do_arch_entry(la, final, disjoint_large_copy_oop_uninit_lsx,          \
                disjoint_large_copy_oop_uninit_lsx,                     \
                disjoint_large_copy_oop_uninit_lsx)                     \
  do_stub(final, conjoint_large_copy_lsx)                               \
  do_arch_entry(la, final, conjoint_large_copy_lsx,                     \
                conjoint_large_copy_lsx, conjoint_large_copy_lsx)       \
  do_stub(final, conjoint_large_copy_oop_lsx)                           \
  do_arch_entry(la, final, conjoint_large_copy_oop_lsx,                 \
                conjoint_large_copy_oop_lsx,                            \
                conjoint_large_copy_oop_lsx)                            \
  do_stub(final, conjoint_large_copy_oop_uninit_lsx)                    \
  do_arch_entry(la, final, conjoint_large_copy_oop_uninit_lsx,          \
                conjoint_large_copy_oop_uninit_lsx,                     \
                conjoint_large_copy_oop_uninit_lsx)                     \
  do_stub(final, disjoint_large_copy_int)                               \
  do_arch_entry(la, final, disjoint_large_copy_int,                     \
                disjoint_large_copy_int, disjoint_large_copy_int)       \
  do_stub(final, disjoint_large_copy_oop)                               \
  do_arch_entry(la, final, disjoint_large_copy_oop,                     \
                disjoint_large_copy_oop,                                \
                disjoint_large_copy_oop)                                \
  do_stub(final, disjoint_large_copy_oop_uninit)                        \
  do_arch_entry(la, final, disjoint_large_copy_oop_uninit,              \
                disjoint_large_copy_oop_uninit,                         \
                disjoint_large_copy_oop_uninit)                         \
  do_stub(final, conjoint_large_copy_int)                               \
  do_arch_entry(la, final, conjoint_large_copy_int,                     \
                conjoint_large_copy_int, conjoint_large_copy_int)       \
  do_stub(final, conjoint_large_copy_oop)                               \
  do_arch_entry(la, final, conjoint_large_copy_oop,                     \
                conjoint_large_copy_oop,                                \
                conjoint_large_copy_oop)                                \
  do_stub(final, conjoint_large_copy_oop_uninit)                        \
  do_arch_entry(la, final, conjoint_large_copy_oop_uninit,              \
                conjoint_large_copy_oop_uninit,                         \
                conjoint_large_copy_oop_uninit)                         \
  do_stub(final, jbyte_small_copy)                                      \
  do_arch_entry(la, final, jbyte_small_copy,                            \
                jbyte_small_copy, jbyte_small_copy)                     \
  do_stub(final, jshort_small_copy)                                     \
  do_arch_entry(la, final, jshort_small_copy,                           \
                jshort_small_copy, jshort_small_copy)                   \
  do_stub(final, jint_small_copy)                                       \
  do_arch_entry(la, final, jint_small_copy,                             \
                jint_small_copy, jint_small_copy)                       \
  do_stub(final, jlong_small_copy)                                      \
  do_arch_entry(la, final, jlong_small_copy,                            \
                jlong_small_copy, jlong_small_copy)                     \
  do_stub(final, jlong_small_copy_oop)                                  \
  do_arch_entry(la, final, jlong_small_copy_oop,                        \
                jlong_small_copy_oop, jlong_small_copy_oop)             \
  do_stub(final, jlong_small_copy_oop_uninit)                           \
  do_arch_entry(la, final, jlong_small_copy_oop_uninit,                 \
                jlong_small_copy_oop_uninit,                            \
                jlong_small_copy_oop_uninit)                            \


#endif // CPU_LOONGARCH_STUBDECLARATIONS_HPP
