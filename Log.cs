using System.Diagnostics;

namespace StringBreaker;

public static class Log {

    [Conditional("DEBUG")]
    public static void WriteLine(string message) {
        //Console.WriteLine(message);
    }

    [Conditional("DEBUG")]
    public static void WriteLine(object message) => WriteLine(message.ToString() ?? "null");
}