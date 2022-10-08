/*
 * Copyright (c) 2020, 2022, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2022, Loongson Technology. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
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
 */

package jdk.internal.foreign.abi.loongarch64.linux;

import jdk.internal.foreign.abi.AbstractLinker;

import java.lang.foreign.*;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodType;
import java.util.function.Consumer;

public final class LinuxLoongArch64Linker extends AbstractLinker {
    static LinuxLoongArch64Linker instance = null;

    public static LinuxLoongArch64Linker getInstance() {
        if (instance == null) {
            instance = new LinuxLoongArch64Linker();
        }
        return instance;
    }

    @Override
    protected MethodHandle arrangeDowncall(MethodType inferredMethodType, FunctionDescriptor function) {
        return CallArranger.arrangeDowncall(inferredMethodType, function);
    }

    @Override
    protected MemorySegment arrangeUpcall(MethodHandle target, MethodType targetType, FunctionDescriptor function, MemorySession scope) {
        return CallArranger.arrangeUpcall(target, targetType, function, scope);
    }

    public static VaList newVaList(Consumer<VaList.Builder> actions, MemorySession scope) {
        LinuxLoongArch64VaList.Builder builder = new LinuxLoongArch64VaList.Builder(scope);
        actions.accept(builder);
        return builder.build();
    }

    public static VaList newVaListOfAddress(MemoryAddress ma, MemorySession session) {
        MemorySegment segment = MemorySegment.ofAddress(ma, Long.MAX_VALUE, session); // size unknown
        return new LinuxLoongArch64VaList(segment, 0);
    }

    public static VaList emptyVaList() {
        return LinuxLoongArch64VaList.empty();
    }
}
