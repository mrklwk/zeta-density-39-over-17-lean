# Reproduce the formalization

Use the committed Lean 4.35.0-rc2 toolchain and exact nine-package lake-manifest.json, including Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55. Keep these pins unchanged.

1. Run `python3 scripts/check_snapshot.py --require-release` to check the source hashes, selected statement surface, import separation, dependency pins and active metadata.
2. With the pinned toolchain installed, run `lake exe cache get`, then `lake build Challenge Solution`. Challenge contains the deliberate statement holes selected by Comparator; Solution must not import Challenge.
3. On Linux with the pinned toolchain and bubblewrap available, run `bash scripts/run_protected_comparator.sh`. It registers the toolchain’s independent kernels in a temporary verifier configuration and uses protected Comparator.
4. Optionally install sympy==1.14.0 in an isolated environment and run `python3 scripts/audit_math.py` for exact rational checks of the displayed formulas, domains and cumulative power curves.

VERIFICATION.json records the completed protected checks on the unchanged proof snapshot and separates them from pending hosted Palomar verification of the final release commit. The three separate-object supplements are outside the 73 selected statements and retain their separate Lean 4.34.1 evidence.
