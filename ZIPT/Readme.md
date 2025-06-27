## ZIPT

ZIPT is a prototype string equation solver in C# build on top Z3.

## Build

Building the solver was tested on Windows with Visual C# Compiler 4.11.0 (Visual Studio 2022) and Debian with .NET 8.0.408.
Further, you need the most current version of [Z3](https://github.com/Z3Prover/z3/). Please compile Z3 (and .NET bindings) on your own and don't take the official release binary. There is a bug.

Open the `ZIPT.sln` solution file with Visual Studio and add a reference to `Microsoft.Z3.dll` or without IDE by specifying the path to `Microsoft.Z3.dll` in ZIPT.csproj

Build the tool either by using Visual Studio or using `dotnet build --configuration Release` in the root directory of the repository. The binary should be placed in `./bin/Release/[your-dotnet-version]/ZIPT.dll` resp., `./bin/Release/[your-dotnet-version]/ZIPT.exe`.

Make sure that `libz3.[dll|so|dylib]` can be found by the problem. You can either install Z3 globally, or copy the `libz3` into the same directory as `ZIPT.dll`.

## Usage

You can then run the program by calling it via command-line arguments.
Depending on your system, you either have to write `dotnet ZIPT.dll [args]` or just `ZIPT.exe [args]`
```
ZIPT.exe [timeout] path-to-smtlib2-file
```

This will instruct the solver to parse and process the given SMT-LIB2 file.

## Limitations

The current state is a prototype. Even though it calls Z3 internally, it might not stably process all kind of inputs. The tool was tested on SMTLIB2 files containing conjunctions of string equations.