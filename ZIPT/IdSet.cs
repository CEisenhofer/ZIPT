using System.Collections.Specialized;
using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace ZIPT;

// This is a bit-string
public struct IdSet {
    uint[] ids;

    public IdSet() {
        ids = [];
    }

    public IdSet(uint[] ids) {
        this.ids = ids;
    }

    public IdSet(in IdSet idSet) {
        ids = new uint[idSet.ids.Length];
        Array.Copy(idSet.ids, ids, idSet.ids.Length);
    }
    
    public IdSet(in IdSet idSet1, in IdSet idSet2) {
        if (idSet2.ids.Length > idSet1.ids.Length) {
            ids = new uint[idSet2.ids.Length];
            Array.Copy(idSet2.ids, ids, idSet2.ids.Length);
            for (int i = 0; i < idSet1.ids.Length; i++) {
                ids[i] |= idSet1.ids[i];
            }
        } else {
            ids = new uint[idSet1.ids.Length];
            Array.Copy(idSet1.ids, ids, idSet1.ids.Length);
            for (int i = 0; i < idSet2.ids.Length; i++) {
                ids[i] |= idSet2.ids[i];
            }
        }
    }

    public void Add(uint id) {
        if (id >= ids.Length * 32) {
            uint[] newIds = new uint[id / 32];
            Array.Copy(ids, newIds, ids.Length);
            ids = newIds;
        }
        ids[id / 32] |= (uint)(1 << (int)(id % 32));
    }

    public void Remove(uint id) {
        if (id < ids.Length * 32)
            ids[id / 32] &= ~(uint)(1 << (int)(id % 32));
    }

    [Pure]
    public bool Contains(uint id) {
        if (id >= ids.Length * 32)
            return false;
        return (ids[id / 32] & (uint)(1 << (int)(id % 32))) != 0;
    }

    public void OrIn(in IdSet other) {
        if (other.ids.Length > ids.Length) {
            uint[] newIds = new uint[other.ids.Length];
            Array.Copy(ids, newIds, ids.Length);
            ids = newIds;
        }
        for (int i = 0; i < other.ids.Length; i++) {
            ids[i] |= other.ids[i];
        }
    }
}