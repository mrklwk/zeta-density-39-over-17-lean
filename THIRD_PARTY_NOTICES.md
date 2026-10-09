# Third-party notices

This notice records upstream attribution and modifications for the included proof
sources. It does not assign a license or authorship to newly written project code.
Existing copyright and author notices in the Lean sources remain applicable.
Paths below are relative to this package unless identified as upstream paths.

## License texts

- [MIT — Scott McColm](licenses/MIT-Scott-McColm.txt): Copyright (c) 2026 Scott McColm.
- [MIT No Attribution — S. McColm](licenses/MIT-0-S-McColm.txt): Copyright 2026 S. McColm.
- [Apache License 2.0](licenses/Apache-2.0.txt): PrimeNumberTheoremAnd and the Grogan source extracts.
- [Mathlib Apache License 2.0](licenses/Mathlib-Apache-2.0.txt): Mathlib and its copied proof fragments.

Identical copies of each license have been consolidated. The Mathlib copy is
retained separately because its appendix text differs from the other Apache copy.
The MIT and MIT-0 notices apply to different upstream revisions; neither replaces
the other.

## Scott McColm: earlier MIT source extracts

Repository: <https://github.com/smccolm/Lean>, revision
`2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`.

Selected proofs from the upstream `Riemann Zeta/RiemannZeta/GuthMaynard/`
source tree are adapted in `lean/MathCollab/Density/`:

| Upstream source | Included adaptation |
| --- | --- |
| `LargeValuesReflection.lean` | `Oscillatory.lean` |
| `ZetaBounds.lean` | `AbelZetaGrowth.lean`, `ZetaJensenInputs.lean` |
| `ZeroCount.lean`, `ExtractSeparated.lean` | `LocalZeroCount.lean` and associated zero-count proofs |
| `ClassicalDensity.lean`, `TypeIICoverage.lean` | `DetectorMellin.lean`, `DetectorContour.lean` and associated detector proofs |

These are extracted and adapted proofs, with changed imports, namespaces,
local interfaces and Lean/Mathlib compatibility changes. The complete MIT
copyright and permission notice is included in the license text linked above.

## S. McColm: MIT-0 sources

Repository: <https://github.com/smccolm/Lean>, revision
`6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1`.

The upstream source root
`Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/71 Guth-Maynard, 2026/`
provides the native density proofs adapted under
`lean/GuthMaynard/NativeSource/GuthMaynard/`, the supporting
`lean/GuthMaynard/NativeSource/CompletedZetaSymmetry.lean` and
`lean/GuthMaynard/NativeSource/FiniteDirichletPolynomial.lean`, the affine extracts under
`lean/GuthMaynard/AffineSource/`, and the classical exponential-sum files
`VanDerCorput`, `SecondDerivative`, `SecondOrderMeanValue`, `Weyl`,
`WeylExplicit` and `WeylZeta` under `lean/GuthMaynard/`.
The affine extracts derive from `LargeValuesAffine.lean`,
`LargeValuesAffineIteration.lean`, `LargeValuesAffineHeight.lean` and their
supporting declarations.

Selected AFE, complex Laplace and growth/occupancy proofs under `lean/WeylPort/`
also derive from this revision. Selected moment source proofs from the upstream
`Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/63 Tao-Trudgian-Yang, 2025/Extension/TaoTrudgianYang2025/`
are extracted and adapted in `lean/MathCollab/Density/Stronger/`.
These source families include additional local proofs and the Apache-licensed
upstream components identified below; this notice does not relicense those parts.

Modifications include extracting declarations, replacing imports, isolating
namespaces (including the native `GuthMaynard.NativeMoment` namespace), removing
blueprint metadata and unrelated dependencies, and adapting proofs and deprecated
syntax to Lean 4.34.1 and the pinned Mathlib version. Local cutoff, coefficient,
error and zeta-assembly proofs supplement these extracts.

## PrimeNumberTheoremAnd (PNT+)

Repository: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>, revision
`4ecb950126c4290293c5662dfe0e884123171df5`. License: Apache 2.0.
Copyright remains with the upstream contributors.

The sources under `lean/GuthMaynard/NativeSource/PrimeNumberTheoremAnd/`
retain the upstream relative module paths. The adapted vendored modules under
`lean/GuthMaynard/NativeSource/GuthMaynardExternal/PNT/` derive from PNT+,
including copies transmitted through McColm's source tree. The source mappings
also include extracted nonstationary-phase, Euler–Maclaurin, zeta-continuation
and digamma proofs under `lean/WeylPort/`, and
`lean/MathCollab/Density/Stronger/Fourth/DigammaSeries.lean`.

The earlier rectangle and contour adaptations in `lean/MathCollab/Density/`,
including `RectangleResidue.lean`, combine the Lean 4.30-compatible rectangle
and contour core from upstream revision `80c12dfd93` with later divisor-support
and rectangle argument-principle developments. The sharp-zeta sources
`ZetaBoundsUpstream.lean` and `ZetaAppendix.lean` derive from the full revision
above. Imports and declaration visibility are adapted to the package's
Lean/Mathlib versions; namespace and API compatibility modifications are local.

Retained source notices include Robby Sneiderman (2026), Matteo Cipollina (2026),
Michael Stoll (2024), James Sundstrom (2024), and Stefan Kebekus (2025).
The digamma source retains “Copyright (c) 2026 Robby Sneiderman” and
“Authors: Robby Sneiderman”. Individual source headers identify the applicable
authors and copyright notices; this list does not replace them.

## Conor Grogan: analytic transform and Gamma extracts

Repository: <https://github.com/jconorgrogan/prime-minor-arcs-2-15>, revision
`f369f267b4dcfebf010c8e7baa2c9602e2960eba`. License: Apache 2.0.
The recorded upstream revision has no root `NOTICE` file, and the selected
source files have no additional copyright or attribution header.

| Upstream source | Included adaptation under `lean/MathCollab/Density/` |
| --- | --- |
| `Proof/GuthMaynardJIterationPoisson.lean` | `AnalyticTransforms.lean` (Poisson and scaled modulation) |
| `Proof/GuthMaynardReflectionMellin.lean` | `AnalyticTransforms.lean` (Mellin inversion) |
| `Proof/GuthMaynardMellinRapidDecay.lean` | `AnalyticTransforms.lean` (logarithmic lift and Mellin decay) |
| `Proof/GammaCompactStrip.lean` | `GammaStrip.lean` |
| `Proof/GammaMellinInversion.lean`, `Proof/MellinDetectorLeaf.lean` | `GammaMellin.lean` |

These are narrow proof extracts with changed namespaces, consolidated Mathlib
imports, local opening declarations and compatibility adaptations. They do not
import the remainder of the upstream project.

## Mathlib

Repository: <https://github.com/leanprover-community/mathlib4>, revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. License: Apache 2.0.
Mathlib is also an external build dependency. Copied or adapted proof fragments
retain their applicable source attribution.

In particular, `lean/WeylPort/AFE/FiniteExponentialSums.lean` adapts the
alternating-series error argument from `Mathlib/Analysis/SpecificLimits/Normed.lean`,
with attribution to Anatole Dedecker, Sébastien Gouëzel, Yury Kudryashov,
Dylan MacKenzie and Patrick Massot. The adaptation uses an ordered limit in
place of unordered summability.

The source adaptations and local modifications described here are not upstream
releases and imply no upstream endorsement.

## Additional selected moment closure

The combined curve includes the native stronger endpoint and its selected fourth- and twelfth-moment, point-mean, Atkinson and peak-counting dependencies under `lean/MathCollab/Density/Stronger/`. The McColm extracts remain attributed to revision `6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1` under MIT-0; PNT and Mathlib portions retain Apache-2.0 and their source notices. Local analytic producers and compositions are not attributed to upstream authors merely by inclusion in that namespace. Public-safe source identity extracts are retained under `third_party/twelfth/`; these contain provenance rather than historical verification claims.
