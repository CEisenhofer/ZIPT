using System.Diagnostics;
using StringBreaker.Constraints;
using StringBreaker.Tokens;

namespace StringBreaker.MiscUtils;

public static class StringUtils {

    // Returns the length l such s = s[0..l]^n for some n > 0
    public static int LeastRepeatedPrefix(Str s) {
        Debug.Assert(s.IsNonEmpty());
        try {
            for (int len = 1; len <= s.Count / 2; len++) {
                if (s.Count % len != 0)
                    continue;
                int i = len;
                for (; i < s.Count; i += len) {
                    int j = 0;
                    for (; j < len; j++) {
                        if (!s[i + j].Equals(s[j]))
                            break;
                    }
                    if (j < len)
                        break;
                }
                if (i >= s.Count)
                    return len;
            }
            return s.Count;
        }
        catch (Exception ex) {
            Console.WriteLine("Exception: " + ex);
            throw;
        }
    }

}