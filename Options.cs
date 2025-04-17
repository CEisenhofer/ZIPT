namespace StringBreaker;

public static class Options {
    public static bool ModelCompletion { get; set; }= true;
    
    static uint reasoningUnwindingBound = 1;
    public static uint ReasoningUnwindingBound
    {
        get => reasoningUnwindingBound;
        set => reasoningUnwindingBound = Math.Max(1, value);
    }
    
    static uint modelUnwindingBound = 1;
    public static uint ModelUnwindingBound
    {
        get => modelUnwindingBound;
        set => modelUnwindingBound = Math.Max(0, value);
    }

    // max number of recursive steps (not a good measure - probably best kept at uint.MaxValue)
    static uint itDeepDepthStart = uint.MaxValue;
    public static uint ItDeepDepthStart {
        get => itDeepDepthStart;
        set => itDeepDepthStart = Math.Max(1, value);
    }

    static uint itDeepeningInc = 1;
    public static uint ItDeepeningInc {
        get => itDeepeningInc;
        set => itDeepeningInc = Math.Max(1, value);
    }

    public static bool GetAndCheckModel { get; set; } = true;

    // Mostly for debug reasons - try to get all consistent Nielsen nodes (might be infinitely many though)
    public static bool FullGraphExpansion { get; set; } = false;
}