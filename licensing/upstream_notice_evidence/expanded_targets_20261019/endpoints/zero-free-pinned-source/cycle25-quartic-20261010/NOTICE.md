# Source notices

Copyright 2026 Hailey Collet. New manuscript and formalization material are
licensed under Apache-2.0. See `LICENSE` and `PROVENANCE.md`.

The vendored `formalization/OAI/` source is the exact import closure from
[OpenAI/math](https://github.com/openai/math) at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. It retains its upstream authorship
and Apache-2.0 license. The source inventory records each included module.
The new proof uses that development's original 7/8 nonvanishing theorem as
a weaker initialization, as well as its analytic and arithmetic foundations.

The `Cycle25` development adapts the numerator inversion, conductor allocation,
coefficient estimates and contour assembly of Akash Levy's
[weighted-numerator proof](https://github.com/akashlevy/QuasiRiemannTracker/tree/2fd60c0926b66ea18d7436f5ed55250fd006ab5d/proofs/akashlevy-20261009-weighted-numerator),
revision `2fd60c0926b66ea18d7436f5ed55250fd006ab5d`, and generalizes the moment,
counting and geometric estimates to the quartic endpoint. That source's
license and notice are retained in `licenses/`; its notice describes the
original upstream package. Its previous final nonvanishing theorem is not
used to establish the new endpoint.

The three `ZetaZeroFree/Analytic/Moments/` modules are reused from Hailey
Collet's [4/33 formalization](https://github.com/GTimG/QuasiRiemannTracker/pull/8).
They reorganize and adapt intermediate OpenAI proofs to establish an
unconditional moving-radical moment. The earlier 4/33 nonvanishing theorem
is not a dependency of this submission.

Mathlib, PrimeNumberTheoremAnd, rellich-kondrachov and the remaining Lake
dependencies retain their own authorship and licenses. Their exact revisions
and the required compatibility patches are recorded with the build recipe.
The patches retain the original licenses; only files needed by this proof's
import closure are included.

Lean, Comparator, NanoDa, con-ron, lean4export and the Palomar verification
helpers are used under their respective licenses. Their binaries are not
redistributed. No upstream project or maintainer endorsement is implied.
