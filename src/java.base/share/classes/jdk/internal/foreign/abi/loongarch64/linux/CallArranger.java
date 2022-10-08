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

import jdk.internal.foreign.PlatformLayouts;
import jdk.internal.foreign.abi.*;

import java.lang.foreign.*;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodType;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static jdk.internal.foreign.abi.loongarch64.LoongArch64Architecture.*;
import static jdk.internal.foreign.abi.loongarch64.linux.TypeClass.*;

/**
 * For the LoongArch64 C ABI specifically, this class uses CallingSequenceBuilder
 * to translate a C FunctionDescriptor into a CallingSequence, which can then be turned into a MethodHandle.
 *
 * This includes taking care of synthetic arguments like pointers to return buffers for 'in-memory' returns.
 */
public class CallArranger {
    private static final int STACK_SLOT_SIZE = 8;
    public static final int MAX_REGISTER_ARGUMENTS = 8;
    private static final ABIDescriptor CLinux = abiFor(
            new VMStorage[]{a0, a1, a2, a3, a4, a5, a6, a7},
            new VMStorage[]{f0, f1, f2, f3, f4, f5, f6, f7},
            new VMStorage[]{a0, a1},
            new VMStorage[]{f0, f1},
            new VMStorage[]{t0, t1, t2, t3, t4, t5, t6, t7, t8},
            new VMStorage[]{f8, f9, f10, f11, f12, f13, f14, f15, f16,
                            f17, f18, f19, f20, f21, f22, f23},
            16, // stackAlignment
            0, // no shadow space
            t4, // target addr reg
            t7  // ret buf addr reg
    );

    // Make registers as prototype, create new register with same index and name but different type.
    // In fact, registers with the same index are the same registers.
    // The field type of VMStorage can encode width information.
    static Map.Entry<Integer, VMStorage[]> buildStorageEntry(int storageClass, VMStorage[][] storagePrototypes) {
        VMStorage[] prototypes = storagePrototypes[storageClass];
        VMStorage[] result = new VMStorage[prototypes.length];
        for (int i = 0; i < prototypes.length; i++) {
            result[i] = new VMStorage(storageClass, prototypes[i].index(), prototypes[i].name());
        }
        return Map.entry(storageClass, result);
    }

    // Registers be used for input arguments.
    static final Map<Integer, VMStorage[]> inputStorage = Map.ofEntries(
            buildStorageEntry(StorageClasses.INTEGER, CLinux.inputStorage),
            buildStorageEntry(StorageClasses.FLOAT, CLinux.inputStorage)
    );

    static Map<Integer, VMStorage[]> outputStorage = Map.ofEntries(
            buildStorageEntry(StorageClasses.INTEGER, CLinux.outputStorage),
            buildStorageEntry(StorageClasses.FLOAT, CLinux.outputStorage)
    );

    public static class Bindings {
        public final CallingSequence callingSequence;
        public final boolean isInMemoryReturn;

        Bindings(CallingSequence callingSequence, boolean isInMemoryReturn) {
            this.callingSequence = callingSequence;
            this.isInMemoryReturn = isInMemoryReturn;
        }
    }

    public static CallArranger.Bindings getBindings(MethodType mt, FunctionDescriptor cDesc, boolean forUpcall) {
        CallingSequenceBuilder csb = new CallingSequenceBuilder(CLinux, forUpcall);
        BindingCalculator argCalc = forUpcall ? new BoxBindingCalculator(true) : new UnboxBindingCalculator(true);
        BindingCalculator retCalc = forUpcall ? new UnboxBindingCalculator(false) : new BoxBindingCalculator(false);

        // When return struct is classified as STRUCT_REFERENCE, it will be true.
        boolean returnInMemory = isInMemoryReturn(cDesc.returnLayout());
        if (returnInMemory) {
            Class<?> carrier = MemoryAddress.class;
            MemoryLayout layout = PlatformLayouts.LinuxLoongArch64.C_POINTER;
            csb.addArgumentBindings(carrier, layout, argCalc.getBindings(carrier, layout, false));
        } else if (cDesc.returnLayout().isPresent()) {
            Class<?> carrier = mt.returnType();
            MemoryLayout layout = cDesc.returnLayout().get();
            csb.setReturnBindings(carrier, layout, retCalc.getBindings(carrier, layout, false));
        }

        for (int i = 0; i < mt.parameterCount(); i++) {
            Class<?> carrier = mt.parameterType(i);
            MemoryLayout layout = cDesc.argumentLayouts().get(i);
            boolean isVar = cDesc.firstVariadicArgumentIndex() != -1 && i >= cDesc.firstVariadicArgumentIndex();
            csb.addArgumentBindings(carrier, layout, argCalc.getBindings(carrier, layout, isVar));
        }

        return new CallArranger.Bindings(csb.build(), returnInMemory);
    }

    public static MethodHandle arrangeDowncall(MethodType mt, FunctionDescriptor cDesc) {
        CallArranger.Bindings bindings = getBindings(mt, cDesc, false);

        MethodHandle handle = new DowncallLinker(CLinux, bindings.callingSequence).getBoundMethodHandle();

        if (bindings.isInMemoryReturn) {
            handle = SharedUtils.adaptDowncallForIMR(handle, cDesc);
        }

        return handle;
    }

    public static MemorySegment arrangeUpcall(MethodHandle target, MethodType mt, FunctionDescriptor cDesc, MemorySession session) {

        CallArranger.Bindings bindings = getBindings(mt, cDesc, true);

        if (bindings.isInMemoryReturn) {
            target = SharedUtils.adaptUpcallForIMR(target, true /* drop return, since we don't have bindings for it */);
        }

        return UpcallLinker.make(CLinux, target, bindings.callingSequence, session);
    }

    private static boolean isInMemoryReturn(Optional<MemoryLayout> returnLayout) {
        return returnLayout
                .filter(GroupLayout.class::isInstance)
                .filter(g -> TypeClass.classifyLayout(g) == TypeClass.STRUCT_REFERENCE)
                .isPresent();
    }

    static class StorageCalculator {
        private final boolean forArguments;
        // next available register index. 0=integerRegIdx, 1=floatRegIdx
        private final int[] nRegs = {0, 0};
        private long stackOffset = 0;

        public StorageCalculator(boolean forArguments) {
            this.forArguments = forArguments;
        }

        VMStorage stackAlloc() {
            assert forArguments : "no stack returns";
            VMStorage storage = stackStorage((int) (stackOffset / STACK_SLOT_SIZE));
            stackOffset += STACK_SLOT_SIZE;
            return storage;
        }

        Optional<VMStorage> regAlloc(int storageType) {
            int allocateType = storageType;
            var availableRegs = MAX_REGISTER_ARGUMENTS - nRegs[allocateType];
            if (availableRegs > 0) {
                VMStorage[] source =
                        (forArguments ? inputStorage : outputStorage).get(storageType);
                Optional<VMStorage> result =
                        Optional.of(source[nRegs[allocateType]]);
                nRegs[allocateType] += 1;
                return result;
            }
            return Optional.empty();
        }

        // Try to get Storage corresponding to storageClass,
        VMStorage getStorage(int storageClass) {
            Optional<VMStorage> storage = regAlloc(storageClass);
            if (storage.isPresent()) return storage.get();
            // If storageClass is FLOAT, and no floating-point register is available,
            // try to allocate an integer register.
            if (storageClass == StorageClasses.FLOAT) {
                storage = regAlloc(StorageClasses.toIntegerClass(storageClass));
                if (storage.isPresent()) return storage.get();
            }
            return stackAlloc();
        }

        VMStorage[] getStorages(MemoryLayout layout) {
            int regCnt = (int) SharedUtils.alignUp(layout.byteSize(), 8) / 8;
            VMStorage[] storages = new VMStorage[regCnt];
            for (int i = 0; i < regCnt; i++) {
                // use integer calling convention.
                storages[i] = getStorage(StorageClasses.INTEGER);
            }
            return storages;
        }

        boolean availableRegs(int integerReg, int floatReg) {
            return nRegs[StorageClasses.INTEGER] + integerReg <= MAX_REGISTER_ARGUMENTS &&
                   nRegs[StorageClasses.FLOAT] + floatReg <= MAX_REGISTER_ARGUMENTS;
        }

        @Override
        public String toString() {
            String nReg = "iReg: " + nRegs[0] + ", fReg: " + nRegs[1];
            String stack = ", stackOffset: " + stackOffset;
            return "{" + nReg + stack + "}";
        }
    }

    abstract static class BindingCalculator {
        protected final StorageCalculator storageCalculator;

        @Override
        public String toString() {
            return storageCalculator.toString();
        }

        protected BindingCalculator(boolean forArguments) {
            this.storageCalculator = new CallArranger.StorageCalculator(forArguments);
        }

        abstract List<Binding> getBindings(Class<?> carrier, MemoryLayout layout, boolean isVariadicArg);

        // Variadic arguments are passed according to the integer calling convention.
        // When handling variadic part, integer calling convention should be used.
        static final Map<TypeClass, TypeClass> conventionConverterMap =
                Map.ofEntries(Map.entry(FLOAT, INTEGER),
                              Map.entry(STRUCT_FA, STRUCT_A),
                              Map.entry(STRUCT_BOTH, STRUCT_A));
    }

    static class UnboxBindingCalculator extends BindingCalculator {
        boolean forArguments;

        UnboxBindingCalculator(boolean forArguments) {
            super(forArguments);
            this.forArguments = forArguments;
        }

        @Override
        List<Binding> getBindings(Class<?> carrier, MemoryLayout layout, boolean isVariadicArg) {
            TypeClass typeClass = TypeClass.classifyLayout(layout);
            if (isVariadicArg) {
                typeClass = BindingCalculator.conventionConverterMap.getOrDefault(typeClass, typeClass);
            }
            return getBindings(carrier, layout, typeClass);
        }

        List<Binding> getBindings(Class<?> carrier, MemoryLayout layout, TypeClass argumentClass) {
            // Binding.Builder will build a series of operation. Its working style like a stack interpreter.
            Binding.Builder bindings = Binding.builder();
            switch (argumentClass) {
                case INTEGER, FLOAT -> {
                    VMStorage storage = storageCalculator.getStorage(StorageClasses.fromTypeClass(argumentClass));
                    bindings.vmStore(storage, carrier);
                }

                case POINTER -> {
                    bindings.unboxAddress(carrier);
                    VMStorage storage = storageCalculator.getStorage(StorageClasses.INTEGER);
                    bindings.vmStore(storage, long.class);
                }

                case STRUCT_A -> {
                    assert carrier == MemorySegment.class;
                    VMStorage[] locations = storageCalculator.getStorages(
                            layout);
                    int locIndex = 0;
                    long offset = 0;
                    while (offset < layout.byteSize()) {
                        final long copy = Math.min(layout.byteSize() - offset, 8);
                        VMStorage storage = locations[locIndex++];
                        boolean useFloat = storage.type() == StorageClasses.FLOAT;
                        Class<?> type = SharedUtils.primitiveCarrierForSize(copy, useFloat);
                        if (offset + copy < layout.byteSize()) {
                            bindings.dup();
                        }
                        bindings.bufferLoad(offset, type)
                                .vmStore(storage, type);
                        offset += copy;
                    }
                }

                case STRUCT_FA -> {
                    assert carrier == MemorySegment.class;
                    List<FlattenedFieldDesc> descs = getFlattenedFields((GroupLayout) layout);
                    if (storageCalculator.availableRegs(0, descs.size())) {
                        for (int i = 0; i < descs.size(); i++) {
                            FlattenedFieldDesc desc = descs.get(i);
                            Class<?> type = desc.layout().carrier();
                            VMStorage storage = storageCalculator.getStorage(
                                    StorageClasses.fromTypeClass(desc.typeClass()));
                            if (i < descs.size() - 1) bindings.dup();
                            bindings.bufferLoad(desc.offset(), type)
                                    .vmStore(storage, type);
                        }
                    } else {
                        // If there is not enough register can be used, then fall back to integer calling convention.
                        return getBindings(carrier, layout, STRUCT_A);
                    }
                }

                case STRUCT_BOTH -> {
                    assert carrier == MemorySegment.class;
                    if (storageCalculator.availableRegs(1, 1)) {
                        List<FlattenedFieldDesc> descs = getFlattenedFields((GroupLayout) layout);
                        for (int i = 0; i < 2; i++) {
                            int storageType = StorageClasses.fromTypeClass(descs.get(i).typeClass());
                            FlattenedFieldDesc desc = descs.get(i);
                            VMStorage storage = storageCalculator.getStorage(storageType);
                            Class<?> type = desc.layout().carrier();
                            if (i < 1) bindings.dup();
                            bindings.bufferLoad(desc.offset(), type)
                                    .vmStore(storage, type);
                        }
                    } else {
                        return getBindings(carrier, layout, STRUCT_A);
                    }
                }

                case STRUCT_REFERENCE -> {
                    assert carrier == MemorySegment.class;
                    bindings.copy(layout)
                            .unboxAddress(MemorySegment.class);
                    VMStorage storage = storageCalculator.getStorage(
                            StorageClasses.INTEGER);
                    bindings.vmStore(storage, long.class);
                }

                default -> throw new UnsupportedOperationException("Unhandled class " + argumentClass);
            }
            return bindings.build();
        }
    }

    static class BoxBindingCalculator extends BindingCalculator {

        BoxBindingCalculator(boolean forArguments) {
            super(forArguments);
        }

        @Override
        List<Binding> getBindings(Class<?> carrier, MemoryLayout layout, boolean isVariadicArg) {
            TypeClass typeClass = TypeClass.classifyLayout(layout);
            if (isVariadicArg) {
                typeClass = BindingCalculator.conventionConverterMap.getOrDefault(typeClass, typeClass);
            }
            return getBindings(carrier, layout, typeClass);
        }

        List<Binding> getBindings(Class<?> carrier, MemoryLayout layout, TypeClass argumentClass) {
            Binding.Builder bindings = Binding.builder();
            switch (argumentClass) {
                case INTEGER, FLOAT -> {
                    VMStorage storage = storageCalculator.getStorage(StorageClasses.fromTypeClass(argumentClass));
                    bindings.vmLoad(storage, carrier);
                }

                case POINTER -> {
                    VMStorage storage = storageCalculator.getStorage(StorageClasses.INTEGER);
                    bindings.vmLoad(storage, long.class)
                            .boxAddress();
                }

                case STRUCT_A -> {
                    assert carrier == MemorySegment.class;
                    bindings.allocate(layout);
                    VMStorage[] locations = storageCalculator.getStorages(
                            layout);
                    int locIndex = 0;
                    long offset = 0;
                    while (offset < layout.byteSize()) {
                        final long copy = Math.min(layout.byteSize() - offset, 8);
                        VMStorage storage = locations[locIndex++];
                        boolean useFloat = storage.type() == StorageClasses.FLOAT;
                        Class<?> type = SharedUtils.primitiveCarrierForSize(copy, useFloat);
                        bindings.dup().vmLoad(storage, type)
                                .bufferStore(offset, type);
                        offset += copy;
                    }
                }

                case STRUCT_FA -> {
                    assert carrier == MemorySegment.class;
                    bindings.allocate(layout);
                    List<FlattenedFieldDesc> descs = getFlattenedFields((GroupLayout) layout);
                    if (storageCalculator.availableRegs(0, descs.size())) {
                        for (FlattenedFieldDesc desc : descs) {
                            Class<?> type = desc.layout().carrier();
                            VMStorage storage = storageCalculator.getStorage(
                                    StorageClasses.fromTypeClass(desc.typeClass()));
                            bindings.dup()
                                    .vmLoad(storage, type)
                                    .bufferStore(desc.offset(), type);
                        }
                    } else {
                        return getBindings(carrier, layout, STRUCT_A);
                    }
                }

                case STRUCT_BOTH -> {
                    assert carrier == MemorySegment.class;
                    bindings.allocate(layout);
                    if (storageCalculator.availableRegs(1, 1)) {
                        List<FlattenedFieldDesc> descs = getFlattenedFields((GroupLayout) layout);
                        for (int i = 0; i < 2; i++) {
                            FlattenedFieldDesc desc = descs.get(i);
                            int storageType = StorageClasses.fromTypeClass(desc.typeClass());
                            VMStorage storage = storageCalculator.getStorage(storageType);
                            Class<?> type = desc.layout().carrier();
                            bindings.dup()
                                    .vmLoad(storage, type)
                                    .bufferStore(desc.offset(), type);
                        }
                    } else {
                        return getBindings(carrier, layout, STRUCT_A);
                    }
                }

                case STRUCT_REFERENCE -> {
                    assert carrier == MemorySegment.class;
                    VMStorage storage = storageCalculator.getStorage(
                            StorageClasses.INTEGER);
                    bindings.vmLoad(storage, long.class)
                            .boxAddress()
                            .toSegment(layout);
                }

                default -> throw new UnsupportedOperationException("Unhandled class " + argumentClass);
            }
            return bindings.build();
        }
    }
}
