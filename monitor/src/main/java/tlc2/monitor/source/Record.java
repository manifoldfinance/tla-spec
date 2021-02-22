/*
 * Copyright 2020-present Open Networking Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package tlc2.monitor.source;

import tlc2.value.IValue;
import tlc2.value.impl.Value;

/**
 * Consumer record.
 */
public class Record {
    private final long index;
    private final IValue value;
    private final long timestamp;

    public Record(long index, IValue value, long timestamp) {
        this.index = index;
        this.value = value;
        this.timestamp = timestamp;
    }

    /**
     * Returns the record index.
     *
     * @return the record index
     */
    public final long index() {
        return index;
    }

    /**
     * Returns the record value.
     *
     * @return the record value
     */
    public final Value value() {
        return (Value) value;
    }

    /**
     * Returns the record timestamp.
     *
     * @return the record timestamp
     */
    public final long timestamp() {
        return timestamp;
    }

    @Override
    public String toString() {
        return String.format("Record(index=%d, value=%s, timestamp=%d)", index, value, timestamp);
    }
}
