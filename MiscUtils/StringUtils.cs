namespace StringBreaker.MiscUtils;

public static class StringUtils {

    public static string LeastRepeatedPrefix(string s) {
        try {
            for (int len = 1; len <= s.Length / 2; len++) {
                if (s.Length % len != 0)
                    continue;
                int i = len;
                for (; i < s.Length; i += len) {
                    int j = 0;
                    for (; j < len; j++) {
                        if (s[i + j] != s[j])
                            break;
                    }
                    if (j < len)
                        break;
                }
                if (i >= s.Length)
                    return s[..len];
            }
            return s;
        }
        catch (Exception ex) {
            Console.WriteLine("Exception: " + ex);
            return LeastRepeatedPrefix(s);
            throw;
        }
    }

}