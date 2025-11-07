namespace ZIPT;

[AttributeUsage(AttributeTargets.Property)]
public class StatAttribute : Attribute {
    public string Name { get; }
    public StatAttribute(string name) => Name = name;
}

public static class Stats {
    [Stat("String Tuples Created")]
    public static int NewStringTuple { get; set; }
    [Stat("String Tuples Reused")]
    public static int CachedStringTuple { get; set; }
    [Stat("Left Drops")]
    public static int StringLeftDropping { get; set; }
    [Stat("Left Drops Reused")]
    public static int CachedStringLeftDropping { get; set; }
    [Stat("Right Drops")]
    public static int StringRightDropping { get; set; }
    [Stat("Right Drops Reused")]
    public static int CachedStringRightDropping { get; set; }
    [Stat("Substitutions")]
    public static int StringSubstitution { get; set; }
    [Stat("Substitutions Reused")]
    public static int CachedStringSubstitution { get; set; }
    [Stat("Simplifications Reused")]
    public static int CachedStringSimplification { get; set; }
    [Stat("Contained Variables Reused")]
    public static int CachedStringVariableContains { get; set; }
    [Stat("First Char Reused")]
    public static int CachedFirstChars { get; set; }
    [Stat("Last Char Reused")]
    public static int CachedLastChars { get; set; }
    [Stat("Sequences Reused")]
    public static int CachedStringSequence { get; set; }
    [Stat("String Rewritings")]
    public static int DegeneratedCnt { get; set; }
}