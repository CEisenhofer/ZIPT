namespace ZIPT;

public static class Options {
    // Global runtime options used by the solver and propagator. Adjust via command line flags
    // or programmatically when embedding the solver.
    public static bool ModelCompletion { get; set; }= false;
    
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

    // TODO: Threshold for |x| = k to symbolic characters

    public static bool CheckModel { get; set; } = false;

    public static bool SaturateGraph { get; set; } = false;

    public static bool OutputModel { get; set; } = false;

    public static bool KeepProof { get; set; } = false;

    public static bool OutputGraph { get; set; } = false;

    public static bool OutputStats { get; set; } = false;

    public const uint MaxCharUtf = 196607;
    public const uint BitsUtf = 18;
    public const uint MaxCharBmp = 65535;
    public const uint BitsBmp = 16;
    public const uint MaxCharAscii = 255;
    public const uint BitsAscii = 8;
    public static uint MaxChar { get; set; } = MaxCharUtf;
    public static uint CharBits { get; set; } = BitsUtf;

    public static int TimeOut { get; set; } = 0;
    public static int MaxDegenerationLevel { get; set; } = 10;

}