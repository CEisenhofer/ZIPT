namespace ZIPT.MiscUtils;

public sealed class SolverTimeoutException : Exception {
    public override string Message => "Timeout";
}