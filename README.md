# Alchemy - Iterative Decompiler

Alchemy is a script for Ghidra that attempts to parse a function's PCode output and generate a new decompiled function that matches the same PCode.

This is accomplished in several steps:
1. Parse a function selected by the user and generate an initial decompilation "context" containing various information from Ghidra.
2. Create a file using information from the context.
3. Compile the file using a user-specified compiler and flags (ideally the same compiler and flags used to generate the target, thus making a perfect match feasible).
4. Compare the two PCodes, and find where the AST is similar or matching. Apply permutations in areas that do not match. Create a new context based on the compiled function.
5. Rinse and repeat 2-4.
