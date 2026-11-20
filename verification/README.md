# Verification

Run `lake exe cache get` and `bash verification/verify.sh` in a fresh checkout.
The script builds the solution and paper index with warnings treated as errors,
then builds the independent challenge. It checks the pinned statement digest,
the types and bodies of the three statement definitions, the theorem type and
the exact axiom report. The generated logs and comparison report are ignored
by Git and remain available in this directory after the run.

`comparator.json` specifies the challenge, solution, theorem name and allowed
axioms for independent comparison and enables the nanoda checker.
