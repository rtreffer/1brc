/*
 *  Copyright 2023 The original authors
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package dev.morling.onebrc;

import sun.misc.Unsafe;

import java.io.IOException;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.lang.reflect.Field;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.channels.FileChannel.MapMode;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.IntStream;

/**
 * This implementation is derived from Thomas Wuerthinger's genius pointer implementation.
 * It uses the awesome SIMD hack from Roy van Rijn.
 * It's (afaik) the first implementation to do a results hash table on a plain memory segment.
 * 
 * Changes:
 * - Port a int SIMD city name scan, add a fnv64 alike hash function.
 * - Use the full fnv64 hash for name comparison.
 * - Use prime number hash table size.
 * 
 * Changelog:
 * - 2024-01-07: Simplistic hashing, inspired by assembly timing. 1 rotate left every 8 chars.
 * - 2024-01-07: YOLO, why use objects if you can use memory and pointers? :)
 *               Added a plain memory hash table (ResultSet). Reworked most parts.
 * - 2024-01-06: Use 8 byte (long) SIMD scan when possible with one final 4 byte scan (int) if needed.
 *               Improves runtime by ~15%
 * - 2024-01-06: Initial version.
 */
public class CalculateAverage_rtreffer {
    private static final String FILE = "./measurements.txt";

    private static final int SEPARATOR_PATTERN = compilePattern((byte) ';');

    private static final int compilePattern(final byte value) {
        return ((int) value << 24) | ((int) value << 16) | ((int) value << 8) | (int) value;
    }

    private static final long SEPARATOR_PATTERN_LONG = compilePatternLong((byte) ';');

    private static final long compilePatternLong(final byte value) {
        return ((long) value << 56) | ((long) value << 48) | ((long) value << 40) | ((long) value << 32)
                | ((long) value << 24) | ((long) value << 16) | ((long) value << 8) | (long) value;
    }

    private static final Unsafe UNSAFE = initUnsafe();

    private static Unsafe initUnsafe() {
        try {
            Field theUnsafe = Unsafe.class.getDeclaredField("theUnsafe");
            theUnsafe.setAccessible(true);
            return (Unsafe) theUnsafe.get(Unsafe.class);
        }
        catch (NoSuchFieldException | IllegalAccessException e) {
            throw new RuntimeException(e);
        }
    }

    // Good sizes for the hash table.
    // Criteria:
    // - Prime number
    // - Growing 2x - 3x
    // - Small enough to fit into L2 cache (~0.5MB per thread)
    private final static int[] RESULT_SET_TABLE_SIZES = {
            31, // fits a memory page at 4096 bytes
            97,
            251,
            751,
            2251,
            6737,
            19997, // enough for 10'000 stations
    };

    // ResultSet is a hash table implemented on a plain memory segment.
    // It is used to collect the results for a single chunk. It supports reshaping on high load.
    private static class ResultSet {
        int sizeIndex;
        int size;
        int entries;
        long memoryAddress;

        private ResultSet() {
            this.sizeIndex = 0;
            this.size = RESULT_SET_TABLE_SIZES[sizeIndex];
            // WARNING: we never FREE this memory, it's a memory leak.
            // But we don't care, we only (re)allocate so many times, and this is small.
            this.memoryAddress = UNSAFE.allocateMemory(size * 124 + 8);
            initMemory();
        }

        private ResultSet(int sizeIndex) {
            this.sizeIndex = sizeIndex;
            this.size = RESULT_SET_TABLE_SIZES[sizeIndex];
            this.memoryAddress = UNSAFE.allocateMemory(size * 124 + 8);
            initMemory();
        }

        private void initMemory() {
            for (int i = 0; i < size; ++i) {
                setCount(i, 0);
            }
        }

        // Memory access functions.
        // The memory layout is:
        // 0: 4 bytes for the count of name occurencies, 0 if bucket is empty
        // 4: 4 bytes for the max temperature
        // 8: 4 bytes for the min temperature
        // 12: 8 bytes for the sum of all temperatures
        // 20: 1 byte for the length of the city name
        // 21: 101 bytes for the city name (with trailing ';'')
        // 124 bytes per bucket

        // helper function to get / put values

        private final int getCount(int index) {
            return UNSAFE.getInt(memoryAddress + index * 124);
        }

        private final void setCount(int index, int value) {
            UNSAFE.putInt(memoryAddress + index * 124, value);
        }

        private final int getMax(int index) {
            return UNSAFE.getInt(memoryAddress + index * 124 + 4);
        }

        private final void setMax(int index, int value) {
            UNSAFE.putInt(memoryAddress + index * 124 + 4, value);
        }

        private final int getMin(int index) {
            return UNSAFE.getInt(memoryAddress + index * 124 + 8);
        }

        private final void setMin(int index, int value) {
            UNSAFE.putInt(memoryAddress + index * 124 + 8, value);
        }

        private final long getSum(int index) {
            return UNSAFE.getLong(memoryAddress + index * 124 + 12);
        }

        private final void setSum(int index, long value) {
            UNSAFE.putLong(memoryAddress + index * 124 + 12, value);
        }

        private final byte getLength(int index) {
            return UNSAFE.getByte(memoryAddress + index * 124 + 20);
        }

        private final void setLength(int index, byte value) {
            UNSAFE.putByte(memoryAddress + index * 124 + 20, value);
        }

        private final long getNameAddress(int index) {
            return memoryAddress + index * 124 + 21;
        }

        private final void addAll(ResultSet other) {
            final long[] hashLength = new long[2];
            for (int i = 0; i < other.size; ++i) {
                int count = other.getCount(i);
                if (count == 0) {
                    continue;
                }
                scanHashDelimiter(other.getNameAddress(i), other.getNameAddress(i) + other.getLength(i) + 9, hashLength);
                add(hashLength[0], other.getNameAddress(i), other.getLength(i), other.getMin(i), other.getMax(i), count, other.getSum(i));
            }
        }

        private final void set(long hash, long nameAddress, byte nameLength, int min, int max, int count, long sum) {
            int index = (int) ((hash & 0x7fffffffffffffffL) % this.size);
            while (true) {
                int currentCount = getCount(index);
                if (currentCount == 0) {
                    // empty bucket
                    setCount(index, count);
                    setMax(index, max);
                    setMin(index, min);
                    setSum(index, sum);
                    UNSAFE.copyMemory(null, nameAddress, null, getNameAddress(index), nameLength + 1);
                    UNSAFE.putByte(getNameAddress(index) + nameLength, (byte) ';');
                    this.setLength(index, nameLength);
                    this.entries++;
                    if (5 * this.entries > 3 * this.size) {
                        reshape();
                    }
                    break;
                }
                else if (unsafeEquals(getNameAddress(index), getLength(index), nameAddress, nameLength)) {
                    // existing bucket
                    setCount(index, count);
                    setMax(index, max);
                    setMin(index, min);
                    setSum(index, sum);
                    break;
                }
                else {
                    // collision, try next
                    index = (index + 1) % size;
                }
            }
        }

        private final void add(long hash, long nameAddress, byte nameLength, int min, int max, int count, long sum) {
            int index = (int) ((hash & 0x7fffffffffffffffL) % this.size);
            while (true) {
                int currentCount = getCount(index);
                if (currentCount == 0) {
                    // empty bucket
                    setCount(index, count);
                    setMax(index, max);
                    setMin(index, min);
                    setSum(index, sum);
                    UNSAFE.copyMemory(null, nameAddress, null, getNameAddress(index), nameLength + 1);
                    UNSAFE.putByte(getNameAddress(index) + nameLength, (byte) ';');
                    this.setLength(index, nameLength);
                    this.entries++;
                    if (3 * this.entries > 2 * this.size) {
                        reshape();
                    }
                    break;
                }
                else if (unsafeEquals(getNameAddress(index), getLength(index), nameAddress, nameLength)) {
                    // existing bucket
                    setCount(index, count + currentCount);
                    setMax(index, Math.max(getMax(index), max));
                    setMin(index, Math.min(getMin(index), min));
                    setSum(index, getSum(index) + sum);
                    break;
                }
                else {
                    // collision, try next
                    index = (index + 1) % size;
                }
            }
        }

        // Add a single entry, returns true if the entry was newly added, false if it was merged.
        private final boolean add(long hash, long nameAddress, byte nameLength, int value) {
            int index = (int) ((hash & 0x7fffffffffffffffL) % this.size);
            int r = 0;
            while (true) {
                int count = getCount(index);
                if (count == 0) {
                    // empty bucket
                    setCount(index, 1);
                    setMax(index, value);
                    setMin(index, value);
                    setSum(index, value);
                    UNSAFE.copyMemory(null, nameAddress, null, getNameAddress(index), nameLength + 1);
                    UNSAFE.putByte(getNameAddress(index) + nameLength, (byte) ';');
                    this.setLength(index, nameLength);
                    this.entries++;
                    if (3 * this.entries > 2 * this.size) {
                        reshape();
                    }
                    return true;
                }
                else if (unsafeEquals(getNameAddress(index), getLength(index), nameAddress, nameLength)) {
                    // existing bucket
                    setCount(index, count + 1);
                    setMax(index, Math.max(getMax(index), value));
                    setMin(index, Math.min(getMin(index), value));
                    setSum(index, getSum(index) + value);
                    return false;
                }
                else {
                    // collision, try next
                    index = (index + 1) % size;
                    r++;
                }
            }
        }

        private final void reshape() {
            sizeIndex = this.sizeIndex + 1;
            if (sizeIndex >= RESULT_SET_TABLE_SIZES.length) {
                throw new IllegalStateException("Too many entries");
            }

            // create a new result set with the next size
            // all fields will be copied at the end 🙃
            ResultSet other = new ResultSet(sizeIndex);

            final long[] hashLength = new long[2];
            for (int i = 0; i < this.size; ++i) {
                int count = getCount(i);
                if (count == 0) {
                    continue;
                }
                scanHashDelimiter(getNameAddress(i), getNameAddress(i) + getLength(i) + 9, hashLength);
                other.set(hashLength[0], getNameAddress(i), getLength(i), getMin(i), getMax(i), count, getSum(i));
            }

            // copy all fields
            this.sizeIndex = other.sizeIndex;
            this.size = other.size;
            this.entries = other.entries;
            this.memoryAddress = other.memoryAddress;
        }

        private final void load(NamedResult result) {
            int index = (int) ((result.hash & 0x7fffffffffffffffL) % this.size);
            while (true) {
                int count = getCount(index);
                if (count == 0) {
                    // empty bucket
                    byte[] bytes = new byte[result.length];
                    UNSAFE.copyMemory(null, result.address, bytes, Unsafe.ARRAY_BYTE_BASE_OFFSET, result.length);
                    var name = new String(bytes, StandardCharsets.UTF_8);

                    throw new IllegalStateException("IMPOSSIBLE: " + name + " not found");
                }
                else if (unsafeEquals(getNameAddress(index), getLength(index), result.address, result.length)) {
                    result.min = getMin(index);
                    result.max = getMax(index);
                    result.sum = getSum(index);
                    result.count = count;
                    return;
                }
                else {
                    // collision, try next
                    index = (index + 1) % size;
                }
            }
        }
    }

    private static class NamedResult {
        int min;
        int max;
        long sum;
        int count;
        final long hash;
        final long address;
        final byte length;
        final ByteBuffer nameCopy;

        private NamedResult(long hash, long address, byte length, int value) {
            this.min = value;
            this.max = value;
            this.sum = value;
            this.count = 1;
            this.hash = hash;
            this.nameCopy = ByteBuffer.allocateDirect(108);
            var segment = MemorySegment.ofBuffer(nameCopy);
            this.address = segment.address();
            this.length = length;
            UNSAFE.copyMemory(address, this.address, length + 1);
        }

        public String toString() {
            return round(((double) min) / 10.0) + "/" + round((((double) sum) / 10.0) / count) + "/" + round(((double) max) / 10.0);
        }

        private static double round(double value) {
            return Math.round(value * 10.0) / 10.0;
        }
    }

    private final static class PartialResult {
        ResultSet results;
        HashMap<String, NamedResult> cities;

        private PartialResult() {
            this.results = new ResultSet();
            this.cities = HashMap.newHashMap(1 << 10);
        }

        private final void addAll(PartialResult other) {
            this.results.addAll(other.results);
            this.cities.putAll(other.cities);
        }

        private final void load() {
            for (Map.Entry<String, NamedResult> entry : cities.entrySet()) {
                results.load(entry.getValue());
            }
        }

        private final void add(long hash, long nameAddress, byte nameLength, int value) {
            final boolean newEntry = results.add(hash, nameAddress, nameLength, value);
            if (!newEntry) {
                return;
            }
            var named = new NamedResult(hash, nameAddress, nameLength, value);
            byte[] bytes = new byte[nameLength];
            UNSAFE.copyMemory(null, nameAddress, bytes, Unsafe.ARRAY_BYTE_BASE_OFFSET, nameLength);
            this.cities.put(new String(bytes, StandardCharsets.UTF_8), named);
        }
    }

    public static void main(String[] args) throws IOException {
        // Calculate input segments.
        int numberOfChunks = Runtime.getRuntime().availableProcessors();
        long[] chunks = getSegments(numberOfChunks);

        // Parallel processing of segments.
        List<PartialResult> allResults = IntStream.range(0, chunks.length - 1).mapToObj(chunkIndex -> {
            var result = new PartialResult();
            parseLoop(chunks[chunkIndex], chunks[chunkIndex + 1], result);
            return result;
        }).parallel().toList();

        var result = allResults.getFirst();
        for (int i = 1; i < allResults.size(); ++i) {
            result.addAll(allResults.get(i));
        }
        result.load();

        // Final output.
        System.out.println(new TreeMap<>(result.cities));
    }

    // SIMD scan for the delimiter ';'. Output needs to be 2 long vars: hash & length
    private final static void scanHashDelimiter(long start, long end, long[] output) {
        final long safeSIMDEnd = end - 8;
        long pos = start;
        long hash = 0;
        while (true) {

            while (pos < safeSIMDEnd) {
                // full long SIMD scan
                // NOTE: due to endianess the result will be inverse.
                // "Munich;0" will be loaded as '0', ';', 'h', 'c', 'i', 'n', 'u', 'M'
                //
                // There is one tricky corner case. We could be unable to read the full end of the string
                // E.g. "Guangzhou;0.0\n" would be split into two chunks:
                // 1. "Guangzho"
                // 2. "u;0.0\n"
                // The second segment is one byte short of 8 bytes, so we need to make sure that our SIMD
                // hashing is compatible with the 4 byte reading.
                final long ob = UNSAFE.getLong(pos);
                final long match = ob ^ SEPARATOR_PATTERN_LONG;
                final long mask = ((match - 0x0101010101010101L) & ~match) & 0x8080808080808080L;
                if (mask == 0) {
                    hash = Long.rotateLeft(hash, 1) ^ ob;
                    pos += 8;
                    continue;
                }
                final int index = Long.numberOfTrailingZeros(mask) >> 3;
                output[1] = (int) (pos - start + index);
                output[0] = Long.rotateLeft(hash, 1) ^ (ob & ((1L << (index << 3)) - 1));
                return;
            }

            // NOTE: we can always read 4 bytes while scanning the city name.
            // That's because the minimum trailer is ";0.0\n" which is 6 characters long.

            // We also know that we can't read 8 bytes, so a single scan is enough.

            final int qb = UNSAFE.getInt(pos);
            int match = qb ^ SEPARATOR_PATTERN;
            int mask = ((match - 0x01010101) & ~match) & 0x80808080;
            final int index = Integer.numberOfTrailingZeros((int) mask) >> 3;
            output[1] = pos - start + index;
            output[0] = Long.rotateLeft(hash, 1) ^ (qb & ((1 << (index << 3)) - 1));
            return;
        }
    }

    private static void parseLoop(long chunkStart, long chunkEnd, PartialResult result) {
        long scanPtr = chunkStart;
        final long[] hashLength = new long[2];
        byte b;
        while (scanPtr < chunkEnd) {
            // Scan city name.
            scanHashDelimiter(scanPtr, chunkEnd, hashLength);

            long nameAddress = scanPtr;
            int addressLength = (int) hashLength[1];
            long hash = hashLength[0];
            scanPtr += addressLength + 1;

            int number;
            byte sign = UNSAFE.getByte(scanPtr++);
            if (sign == '-') {
                number = UNSAFE.getByte(scanPtr++) - '0';
                if ((b = UNSAFE.getByte(scanPtr++)) != '.') {
                    number = number * 10 + (b - '0');
                    scanPtr++;
                }
                number = number * 10 + (UNSAFE.getByte(scanPtr++) - '0');
                number = -number;
            }
            else {
                number = sign - '0';
                if ((b = UNSAFE.getByte(scanPtr++)) != '.') {
                    number = number * 10 + (b - '0');
                    scanPtr++;
                }
                number = number * 10 + (UNSAFE.getByte(scanPtr++) - '0');
            }

            result.add(hash, nameAddress, (byte) addressLength, number);

            scanPtr++;
        }
    }

    static boolean unsafeEquals(long aStart, long aLength, long bStart, long bLength) {
        if (aLength != bLength) {
            return false;
        }
        for (int i = 0; i < aLength; ++i) {
            if (UNSAFE.getByte(aStart + i) != UNSAFE.getByte(bStart + i)) {
                return false;
            }
        }
        return true;
    }

    private static long[] getSegments(int numberOfChunks) throws IOException {
        try (var fileChannel = FileChannel.open(Path.of(FILE), StandardOpenOption.READ)) {
            long fileSize = fileChannel.size();
            long segmentSize = (fileSize + numberOfChunks - 1) / numberOfChunks;
            long[] chunks = new long[numberOfChunks + 1];
            MemorySegment segment = fileChannel.map(MapMode.READ_ONLY, 0, fileSize, Arena.global());
            long mappedAddress = segment.address();
            chunks[0] = mappedAddress;
            long endAddress = mappedAddress + fileSize;
            for (int i = 1; i < numberOfChunks; ++i) {
                long chunkAddress = mappedAddress + i * segmentSize;
                // Align to first row start.
                while (chunkAddress < endAddress && UNSAFE.getByte(chunkAddress++) != '\n') {
                    // nop
                }
                chunks[i] = Math.min(chunkAddress, endAddress);
            }
            chunks[numberOfChunks] = endAddress;
            return chunks;
        }
    }
}
