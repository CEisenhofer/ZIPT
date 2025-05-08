using System.Diagnostics;
using System.Runtime.CompilerServices;

namespace StringBreaker;

public static class Log {

    [Conditional("DEBUG")]
    public static void WriteLine(string message) {
        //Console.WriteLine(message);
    }

    [Conditional("DEBUG")]
    public static void WriteLine(object message) => WriteLine(message.ToString() ?? "null");

#if DEBUG
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Verify(bool cond) {
        Debug.Assert(cond);
    }
#else
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Verify(bool cond) {
        //  empty, but cond is evaluated for the side-condition
    }
#endif
}