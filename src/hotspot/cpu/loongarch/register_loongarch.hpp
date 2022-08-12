/*
 * Copyright (c) 2000, 2012, Oracle and/or its affiliates. All rights reserved.
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

#ifndef CPU_LOONGARCH_REGISTER_LOONGARCH_HPP
#define CPU_LOONGARCH_REGISTER_LOONGARCH_HPP

#include "asm/register.hpp"
#include "logging/log.hpp"
#include "utilities/bitMap.hpp"
#include "utilities/formatBuffer.hpp"
#include "utilities/ticks.hpp"

class VMRegImpl;
typedef VMRegImpl* VMReg;

// Use Register as shortcut
class RegisterImpl;
typedef const RegisterImpl* Register;

inline constexpr Register as_Register(int encoding);

class RegisterImpl: public AbstractRegisterImpl {
  static constexpr Register first();

 public:
  enum {
    number_of_registers     = 32,
    max_slots_per_register  = 2
  };

  // derived registers, offsets, and addresses
  const Register successor() const { return this + 1; }

  // construction
  inline friend constexpr Register as_Register(int encoding);

  VMReg as_VMReg() const;

  // accessors
  int encoding() const            { assert(is_valid(), "invalid register"); return encoding_nocheck(); }
  int encoding_nocheck() const    { return this - first(); }
  bool is_valid() const           { return (unsigned)encoding_nocheck() < number_of_registers; }
  const char* name() const;
};

REGISTER_IMPL_DECLARATION(Register, RegisterImpl, RegisterImpl::number_of_registers);

// The integer registers of the LoongArch architecture

CONSTANT_REGISTER_DECLARATION(Register, noreg, (-1));
CONSTANT_REGISTER_DECLARATION(Register, r0,    (0));
CONSTANT_REGISTER_DECLARATION(Register, r1,    (1));
CONSTANT_REGISTER_DECLARATION(Register, r2,    (2));
CONSTANT_REGISTER_DECLARATION(Register, r3,    (3));
CONSTANT_REGISTER_DECLARATION(Register, r4,    (4));
CONSTANT_REGISTER_DECLARATION(Register, r5,    (5));
CONSTANT_REGISTER_DECLARATION(Register, r6,    (6));
CONSTANT_REGISTER_DECLARATION(Register, r7,    (7));
CONSTANT_REGISTER_DECLARATION(Register, r8,    (8));
CONSTANT_REGISTER_DECLARATION(Register, r9,    (9));
CONSTANT_REGISTER_DECLARATION(Register, r10,   (10));
CONSTANT_REGISTER_DECLARATION(Register, r11,   (11));
CONSTANT_REGISTER_DECLARATION(Register, r12,   (12));
CONSTANT_REGISTER_DECLARATION(Register, r13,   (13));
CONSTANT_REGISTER_DECLARATION(Register, r14,   (14));
CONSTANT_REGISTER_DECLARATION(Register, r15,   (15));
CONSTANT_REGISTER_DECLARATION(Register, r16,   (16));
CONSTANT_REGISTER_DECLARATION(Register, r17,   (17));
CONSTANT_REGISTER_DECLARATION(Register, r18,   (18));
CONSTANT_REGISTER_DECLARATION(Register, r19,   (19));
CONSTANT_REGISTER_DECLARATION(Register, r20,   (20));
CONSTANT_REGISTER_DECLARATION(Register, r21,   (21));
CONSTANT_REGISTER_DECLARATION(Register, r22,   (22));
CONSTANT_REGISTER_DECLARATION(Register, r23,   (23));
CONSTANT_REGISTER_DECLARATION(Register, r24,   (24));
CONSTANT_REGISTER_DECLARATION(Register, r25,   (25));
CONSTANT_REGISTER_DECLARATION(Register, r26,   (26));
CONSTANT_REGISTER_DECLARATION(Register, r27,   (27));
CONSTANT_REGISTER_DECLARATION(Register, r28,   (28));
CONSTANT_REGISTER_DECLARATION(Register, r29,   (29));
CONSTANT_REGISTER_DECLARATION(Register, r30,   (30));
CONSTANT_REGISTER_DECLARATION(Register, r31,   (31));

#ifndef DONT_USE_REGISTER_DEFINES
REGISTER_DECLARATION(Register, NOREG, noreg);
REGISTER_DECLARATION(Register, R0,    r0);
REGISTER_DECLARATION(Register, R1,    r1);
REGISTER_DECLARATION(Register, R2,    r2);
REGISTER_DECLARATION(Register, R3,    r3);
REGISTER_DECLARATION(Register, R4,    r4);
REGISTER_DECLARATION(Register, R5,    r5);
REGISTER_DECLARATION(Register, R6,    r6);
REGISTER_DECLARATION(Register, R7,    r7);
REGISTER_DECLARATION(Register, R8,    r8);
REGISTER_DECLARATION(Register, R9,    r9);
REGISTER_DECLARATION(Register, R10,   r10);
REGISTER_DECLARATION(Register, R11,   r11);
REGISTER_DECLARATION(Register, R12,   r12);
REGISTER_DECLARATION(Register, R13,   r13);
REGISTER_DECLARATION(Register, R14,   r14);
REGISTER_DECLARATION(Register, R15,   r15);
REGISTER_DECLARATION(Register, R16,   r16);
REGISTER_DECLARATION(Register, R17,   r17);
REGISTER_DECLARATION(Register, R18,   r18);
REGISTER_DECLARATION(Register, R19,   r19);
REGISTER_DECLARATION(Register, R20,   r20);
REGISTER_DECLARATION(Register, R21,   r21);
REGISTER_DECLARATION(Register, R22,   r22);
REGISTER_DECLARATION(Register, R23,   r23);
REGISTER_DECLARATION(Register, R24,   r24);
REGISTER_DECLARATION(Register, R25,   r25);
REGISTER_DECLARATION(Register, R26,   r26);
REGISTER_DECLARATION(Register, R27,   r27);
REGISTER_DECLARATION(Register, R28,   r28);
REGISTER_DECLARATION(Register, R29,   r29);
REGISTER_DECLARATION(Register, R30,   r30);
REGISTER_DECLARATION(Register, R31,   r31);

#define RA           R1
#define TP           R2
#define SP           R3
#define RA0          R4
#define RA1          R5
#define RA2          R6
#define RA3          R7
#define RA4          R8
#define RA5          R9
#define RA6          R10
#define RA7          R11
#define RT0          R12
#define RT1          R13
#define RT2          R14
#define RT3          R15
#define RT4          R16
#define RT5          R17
#define RT6          R18
#define RT7          R19
#define RT8          R20
#define RX           R21
#define FP           R22
#define S0           R23
#define S1           R24
#define S2           R25
#define S3           R26
#define S4           R27
#define S5           R28
#define S6           R29
#define S7           R30
#define S8           R31

#define Rmethod       S3
#define Rsender       S4
#define Rnext         S1

#define V0       RA0
#define V1       RA1

#define SCR1     RT7
#define SCR2     RT4

//for interpreter frame
// bytecode pointer register
#define BCP            S0
// local variable pointer register
#define LVP            S7
// temporary callee saved register, we use this register to save the register maybe blowed cross call_VM
// be sure to save and restore its value in call_stub
#define TSR            S2

#define TREG           S6

#define S5_heapbase    S5

#define FSR            V0
#define SSR            T6
#define FSF            FV0

#define RECEIVER       T0
#define IC_Klass       T1

#define SHIFT_count    T3

// ---------- Scratch Register ----------
#define AT             RT7
#define fscratch       F23

#endif // DONT_USE_REGISTER_DEFINES

// Use FloatRegister as shortcut
class FloatRegisterImpl;
typedef const FloatRegisterImpl* FloatRegister;

inline constexpr FloatRegister as_FloatRegister(int encoding);

// The implementation of floating point registers for the architecture
class FloatRegisterImpl: public AbstractRegisterImpl {
  static constexpr FloatRegister first();

 public:
  enum {
    number_of_registers     = 32,
    save_slots_per_register = 2,
    slots_per_lsx_register  = 4,
    slots_per_lasx_register = 8,
    max_slots_per_register  = 8
  };

  // construction
  inline friend constexpr FloatRegister as_FloatRegister(int encoding);

  VMReg as_VMReg() const;

  // derived registers, offsets, and addresses
  FloatRegister successor() const {
    return as_FloatRegister((encoding() + 1) % (unsigned)number_of_registers);
  }

  // accessors
  int encoding() const            { assert(is_valid(), "invalid register"); return encoding_nocheck(); }
  int encoding_nocheck() const    { return this - first(); }
  int is_valid() const            { return (unsigned)encoding_nocheck() < number_of_registers; }
  const char* name() const;
};

REGISTER_IMPL_DECLARATION(FloatRegister, FloatRegisterImpl, FloatRegisterImpl::number_of_registers);

CONSTANT_REGISTER_DECLARATION(FloatRegister, fnoreg , (-1));

CONSTANT_REGISTER_DECLARATION(FloatRegister, f0     , ( 0));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f1     , ( 1));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f2     , ( 2));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f3     , ( 3));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f4     , ( 4));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f5     , ( 5));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f6     , ( 6));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f7     , ( 7));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f8     , ( 8));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f9     , ( 9));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f10    , (10));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f11    , (11));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f12    , (12));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f13    , (13));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f14    , (14));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f15    , (15));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f16    , (16));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f17    , (17));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f18    , (18));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f19    , (19));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f20    , (20));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f21    , (21));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f22    , (22));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f23    , (23));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f24    , (24));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f25    , (25));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f26    , (26));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f27    , (27));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f28    , (28));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f29    , (29));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f30    , (30));
CONSTANT_REGISTER_DECLARATION(FloatRegister, f31    , (31));

#ifndef DONT_USE_REGISTER_DEFINES
REGISTER_DECLARATION(FloatRegister, FNOREG, fnoreg);
REGISTER_DECLARATION(FloatRegister, F0, f0);
REGISTER_DECLARATION(FloatRegister, F1, f1);
REGISTER_DECLARATION(FloatRegister, F2, f2);
REGISTER_DECLARATION(FloatRegister, F3, f3);
REGISTER_DECLARATION(FloatRegister, F4, f4);
REGISTER_DECLARATION(FloatRegister, F5, f5);
REGISTER_DECLARATION(FloatRegister, F6, f6);
REGISTER_DECLARATION(FloatRegister, F7, f7);
REGISTER_DECLARATION(FloatRegister, F8, f8);
REGISTER_DECLARATION(FloatRegister, F9, f9);
REGISTER_DECLARATION(FloatRegister, F10, f10);
REGISTER_DECLARATION(FloatRegister, F11, f11);
REGISTER_DECLARATION(FloatRegister, F12, f12);
REGISTER_DECLARATION(FloatRegister, F13, f13);
REGISTER_DECLARATION(FloatRegister, F14, f14);
REGISTER_DECLARATION(FloatRegister, F15, f15);
REGISTER_DECLARATION(FloatRegister, F16, f16);
REGISTER_DECLARATION(FloatRegister, F17, f17);
REGISTER_DECLARATION(FloatRegister, F18, f18);
REGISTER_DECLARATION(FloatRegister, F19, f19);
REGISTER_DECLARATION(FloatRegister, F20, f20);
REGISTER_DECLARATION(FloatRegister, F21, f21);
REGISTER_DECLARATION(FloatRegister, F22, f22);
REGISTER_DECLARATION(FloatRegister, F23, f23);
REGISTER_DECLARATION(FloatRegister, F24, f24);
REGISTER_DECLARATION(FloatRegister, F25, f25);
REGISTER_DECLARATION(FloatRegister, F26, f26);
REGISTER_DECLARATION(FloatRegister, F27, f27);
REGISTER_DECLARATION(FloatRegister, F28, f28);
REGISTER_DECLARATION(FloatRegister, F29, f29);
REGISTER_DECLARATION(FloatRegister, F30, f30);
REGISTER_DECLARATION(FloatRegister, F31, f31);

#define FA0    F0
#define FA1    F1
#define FA2    F2
#define FA3    F3
#define FA4    F4
#define FA5    F5
#define FA6    F6
#define FA7    F7

#define FV0    F0
#define FV1    F1

#define FT0    F8
#define FT1    F9
#define FT2    F10
#define FT3    F11
#define FT4    F12
#define FT5    F13
#define FT6    F14
#define FT7    F15
#define FT8    F16
#define FT9    F17
#define FT10   F18
#define FT11   F19
#define FT12   F20
#define FT13   F21
#define FT14   F22
#define FT15   F23

#define FS0    F24
#define FS1    F25
#define FS2    F26
#define FS3    F27
#define FS4    F28
#define FS5    F29
#define FS6    F30
#define FS7    F31

#endif // DONT_USE_REGISTER_DEFINES

// Use ConditionalFlagRegister as shortcut
class ConditionalFlagRegisterImpl;
typedef const ConditionalFlagRegisterImpl* ConditionalFlagRegister;

inline constexpr ConditionalFlagRegister as_ConditionalFlagRegister(int encoding);

// The implementation of conditional floating point registers
class ConditionalFlagRegisterImpl: public AbstractRegisterImpl {
  static constexpr ConditionalFlagRegister first();

 public:
  enum {
    number_of_registers = 8
  };

  // construction
  inline friend constexpr ConditionalFlagRegister as_ConditionalFlagRegister(int encoding);

  VMReg as_VMReg() const;

  // derived registers, offsets, and addresses
  ConditionalFlagRegister successor() const { return this + 1; }

  // accessors
  int encoding() const            { assert(is_valid(), "invalid register"); return encoding_nocheck(); }
  int encoding_nocheck() const    { return this - first(); }
  bool is_valid() const           { return (unsigned)encoding_nocheck() < number_of_registers; }
  const char* name() const;

};

REGISTER_IMPL_DECLARATION(ConditionalFlagRegister, ConditionalFlagRegisterImpl, ConditionalFlagRegisterImpl::number_of_registers);

CONSTANT_REGISTER_DECLARATION(ConditionalFlagRegister, fccnoreg , (-1));
CONSTANT_REGISTER_DECLARATION(ConditionalFlagRegister, fcc0     , ( 0));
CONSTANT_REGISTER_DECLARATION(ConditionalFlagRegister, fcc1     , ( 1));
CONSTANT_REGISTER_DECLARATION(ConditionalFlagRegister, fcc2     , ( 2));
CONSTANT_REGISTER_DECLARATION(ConditionalFlagRegister, fcc3     , ( 3));
CONSTANT_REGISTER_DECLARATION(ConditionalFlagRegister, fcc4     , ( 4));
CONSTANT_REGISTER_DECLARATION(ConditionalFlagRegister, fcc5     , ( 5));
CONSTANT_REGISTER_DECLARATION(ConditionalFlagRegister, fcc6     , ( 6));
CONSTANT_REGISTER_DECLARATION(ConditionalFlagRegister, fcc7     , ( 7));

#ifndef DONT_USE_REGISTER_DEFINES
REGISTER_DECLARATION(ConditionalFlagRegister, FCCNOREG, fccnoreg);
REGISTER_DECLARATION(ConditionalFlagRegister, FCC0,     fcc0);
REGISTER_DECLARATION(ConditionalFlagRegister, FCC1,     fcc1);
REGISTER_DECLARATION(ConditionalFlagRegister, FCC2,     fcc2);
REGISTER_DECLARATION(ConditionalFlagRegister, FCC3,     fcc3);
REGISTER_DECLARATION(ConditionalFlagRegister, FCC4,     fcc4);
REGISTER_DECLARATION(ConditionalFlagRegister, FCC5,     fcc5);
REGISTER_DECLARATION(ConditionalFlagRegister, FCC6,     fcc6);
REGISTER_DECLARATION(ConditionalFlagRegister, FCC7,     fcc7);
#endif // DONT_USE_REGISTER_DEFINES

// Need to know the total number of registers of all sorts for SharedInfo.
// Define a class that exports it.
class ConcreteRegisterImpl : public AbstractRegisterImpl {
 public:
  enum {
  // A big enough number for C2: all the registers plus flags
  // This number must be large enough to cover REG_COUNT (defined by c2) registers.
  // There is no requirement that any ordering here matches any ordering c2 gives
  // it's optoregs.
    number_of_registers = RegisterImpl::max_slots_per_register * RegisterImpl::number_of_registers +
                          FloatRegisterImpl::max_slots_per_register * FloatRegisterImpl::number_of_registers
  };

  static const int max_gpr;
  static const int max_fpr;
};

typedef AbstractRegSet<Register> RegSet;
typedef AbstractRegSet<FloatRegister> FloatRegSet;

#endif //CPU_LOONGARCH_REGISTER_LOONGARCH_HPP
