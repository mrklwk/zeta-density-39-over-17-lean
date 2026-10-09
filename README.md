# Zero-density estimates from an improved large-values bound

**Author: Mark Lewko**

This project combines a uniform 39/17 zero-density theorem with a more precise
piecewise density curve and a middle-range large-values estimate. The complete
abstract is in [ABSTRACT.md](ABSTRACT.md).

## Zero-density results

For every ε > 0 there is Cε > 0 such that, simultaneously for
1/2 ≤ σ ≤ 1 and T ≥ 2,

\[
N(\sigma,T)\le C_\varepsilon T^{(39/17)(1-\sigma)+\varepsilon}.
\]

The theorem is `GuthMaynard.Improvement.global_density_uniform`.
Its constant is chosen before both σ and T.

For each fixed σ in [1/2,1] and every ε > 0,
`GuthMaynard.Improvement.combined_density_curve` also proves

\[
N(\sigma,T)\le C_{\sigma,\varepsilon}T^{f(\sigma)+\varepsilon},\qquad T\ge2,
\]

where the full exponent f is:

| σ interval | f(σ) |
| --- | --- |
| [1/2,9/13] | 3(1−σ)/(2−σ) |
| (9/13,5/7] | 18(1−σ)/(7σ+3) |
| (5/7,3/4] | (9/4)(1−σ) |
| (3/4,1] | 3(1−σ)/(2σ) |

For the sharper piecewise statement, the constant may depend on σ and ε.
`full_density_curve_uniform_left` supplies one Cε for σ in [1/2,3/4].
`combined_density_curve_uniform_away_boundary` supplies one Cδ,ε for σ in
[1/2,3/4] ∪ [3/4+δ,1], for any fixed δ > 0. These names are in the same
`GuthMaynard.Improvement` namespace. Their constants precede σ and T.

One constant for this exact piecewise exponent over the entire strip has not
been proved. At σ = 3/4, f(σ) = 9/16, whereas its right limit is 1/2.
This limitation does not affect the separate uniform 39/17 theorem.
The other endpoint values at 1/2, 9/13, 5/7 and 1 are 1, 12/17, 9/14 and 0.

For 1/2 ≤ σ < 1 the coefficient f(σ)/(1−σ) has maximum 39/17, attained at 9/13.
The coefficient 9/4 holds only on the indicated upper-middle interval (and
at 5/7). No global fixed-σ or uniform 9/4 result is claimed. This is a maximum
of the proved coefficient envelope, not a claim about the optimal exponent
for the zeta function. No comprehensive novelty claim is made.

Here `MathCollab.Density.zetaDensityCount σ T` counts the zeros of mathlib's
`riemannZeta` satisfying 0 < Re ρ < 1, σ ≤ Re ρ and |Im ρ| ≤ T,
weighted by `analyticOrderNatAt riemannZeta ρ`. The zero set is proved finite.
Both ordinate signs, real-part equality and both height endpoints are included.
At σ = 1 this count is zero.

The 30/13 comparison in the abstract refers to Guth and Maynard,
[New large value estimates for Dirichlet polynomials](https://annals.math.princeton.edu/2026/203-2/p06).
It compares these global coefficient bounds, without asserting pointwise
superiority over every known estimate.

## Middle-range large values

`GuthMaynard.Improvement.middle_range_large_values` proves the proposition
`CandidateMiddleRangeEstimate` (the name is retained for source compatibility).
For every ε > 0 there is Cε > 0 such that, for all real N,T,V,t₀, coefficients
`a : ℕ → ℂ`, and finite sets `W : Finset ℝ`, the following hypotheses imply the
bound below:

- N ≥ 2 and N^(6/5) ≤ T ≤ N^(5/3);
- V > 0 and |aₙ| ≤ 1 for integers N < n ≤ 2N;
- W ⊆ [t₀,t₀+T], and distinct points of W are at least 1 apart;
- |D(t)| ≥ V for every t ∈ W, where
  D(t) = ∑_{⌊N⌋₊ < n ≤ ⌊2N⌋₊} aₙ exp(i t log(n/N)).

\[
|W|\le C_\varepsilon N^\varepsilon
\left(\frac{N^2}{V^2}+\frac{N^{18/7}T^{6/7}}{V^4}\right).
\]

Cε precedes all scales, thresholds, translates, coefficients and point sets.
The normalized polynomial differs from ∑ aₙ exp(i t log n) by the common
unit factor exp(−i t log N), so their norms agree. The source interval is
dyadic (N,2N]. None of the advertised endpoint theorems
has an unproved analytic estimate as a premise.

## Build and checks

This private compatibility migration passed the local checks summarized in
`VERIFICATION.json`, including fresh kernel replay and sandboxed Lean/NanoDa
Comparator checks. The full hosted Palomar preflight has not run. The
verified public Lean 4.34.1 release remains available at commit
`6a2c941b69f2ae91bfa0a63a8b867bfa829db6df`. Its receipts do not certify this migration.

The project lives in `lean/`. It uses Lean 4.35.0-rc2 and mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; `lake-manifest.json` locks
transitive revisions. With that toolchain and the locked dependencies available:

```sh
cd lean
lake build MathCollab GuthMaynard WeylPort Solution VerificationStatements Challenge
lake env lean -DwarningAsError=true -DautoImplicit=false ../verification/StatementChecks.lean
lake env lean -DwarningAsError=true -DautoImplicit=false ../verification/TrustReplay.lean
lake env lean -DwarningAsError=true -DautoImplicit=false ../verification/CoefficientChecks.lean
```

This private migration contains 823 production Lean sources plus three interface
and verification modules, including the selected stronger
endpoint dependency closure. The default target registers all packaged
GuthMaynard submodules and their MathCollab and WeylPort dependencies. External
dependency trees and build caches are not bundled. `SOURCE_INVENTORY.json`
records source identities. `VERIFICATION.json` records completed checks and
clearly separates inherited evidence from this candidate's checks.

The statement probe expands the actual-zero count and compares theorem types.
The strict kernel replay checks the advertised theorem dependency closure,
allowing only `propext`, `Classical.choice` and `Quot.sound`, and rejecting
unsafe or partial declarations. Deprecated-import warnings can remain nonfatal
even with `warningAsError=true`; no warning-free-build claim is made.

## Attribution and review scope

The formalization was developed with AI assistance and incorporates adapted
upstream proofs, with attribution and
applicable licenses retained in `THIRD_PARTY_NOTICES.md`, source headers and
`licenses/`. Independent AI-assisted internal review checked the full-curve statements,
constant dependence, endpoint composition and supporting source inventories.
This is not human peer review or a new line-by-line audit of every imported
analytic proof. No comprehensive novelty claim is made.

New project material is licensed under AGPL-3.0-only. Upstream material retains
its existing licenses and attribution; see [LICENSING.md](LICENSING.md),
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), and the source notices.
