/*
 * Copyright (c) 2003, 2012, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2015, 2026, Loongson Technology. All rights reserved.
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

package sun.jvm.hotspot.debugger.linux.loongarch64;

import sun.jvm.hotspot.debugger.*;
import sun.jvm.hotspot.debugger.linux.*;
import sun.jvm.hotspot.debugger.cdbg.*;
import sun.jvm.hotspot.debugger.cdbg.basic.*;
import sun.jvm.hotspot.debugger.loongarch64.*;
import sun.jvm.hotspot.runtime.*;
import sun.jvm.hotspot.runtime.loongarch64.*;

final public class LinuxLOONGARCH64CFrame extends BasicCFrame {
   // package/class internals only
   public LinuxLOONGARCH64CFrame(LinuxDebugger dbg, Address sp, Address fp, Address pc) {
      super(dbg.getCDebugger());
      this.sp = sp;
      this.fp = fp;
      this.pc = pc;
      this.dbg = dbg;
   }

   // override base class impl to avoid ELF parsing
   public ClosestSymbol closestSymbolToPC() {
      // try native lookup in debugger.
      return dbg.lookup(dbg.getAddressValue(pc()));
   }

   public Address pc() {
      return pc;
   }

   public Address localVariableBase() {
      return fp;
   }

   @Override
   public CFrame sender(ThreadProxy thread) {
      return sender(thread, null, null, null);
   }

   @Override
   public CFrame sender(ThreadProxy thread, Address nextSP, Address nextFP, Address nextPC) {
      // Check fp
      // Skip if both nextFP and nextPC are given - do not need to load from fp.
      if (nextFP == null && nextPC == null) {
        if (fp == null) {
          return null;
        }

        // Check alignment of fp
        if (dbg.getAddressValue(fp) % (2 * ADDRESS_SIZE) != 0) {
          return null;
        }
      }

      if (nextSP == null) {
        nextSP = fp.getAddressAt(0 * ADDRESS_SIZE);
      }
      if (nextSP == null) {
        return null;
      }

      if (nextFP == null) {
        nextFP = fp.getAddressAt(-2 * ADDRESS_SIZE);
      }
      if (nextFP == null) {
        return null;
      }

      if (nextPC == null) {
        nextPC = fp.getAddressAt(-1 * ADDRESS_SIZE);
      }
      if (nextPC == null) {
        return null;
      }

      return new LinuxLOONGARCH64CFrame(dbg, nextSP, nextFP, nextPC);
   }

   @Override
   public Frame toFrame() {
      return new LOONGARCH64Frame(sp, fp, pc);
   }

   private static final int ADDRESS_SIZE = 8;
   private Address pc;
   private Address sp;
   private Address fp;
   private LinuxDebugger dbg;
}
