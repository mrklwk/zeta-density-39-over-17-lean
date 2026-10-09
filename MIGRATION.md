# Private Palomar compatibility candidate

Base: public commit `6a2c941b69f2ae91bfa0a63a8b867bfa829db6df`.
This candidate has not been published or submitted. The base release is unchanged.
All-module build, statement/coefficient checks, fresh 15-root kernel replay and
sandboxed Comparator with Lean and NanoDa passed; see `VERIFICATION.json`.
Comparator reused the freshly built, hash-matched project artifacts. The full
hosted preflight, including a fresh license-detector match, remains outstanding.

## Changes

- Lean 4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, using existing installed tools and pinned dependencies.
- Module declarations and public imports/sections, preserving proof bodies except two deprecated `rwa` uses replaced by `rw` followed by `assumption`.
- The oversized `MediumTypeIEndpoint` file is split at a declaration boundary into a foundation module and its existing consumer. Recombining the two original portions reproduces the original source.
- Helpers used in public types or exposed definitions are made public: `centralPoint`, `gammaDenom`, `typeIDyadicCutoffComplex`, and the four normalized-kernel continuity/compact-support helpers. Their bodies are unchanged.
- `GammaPhase` explicitly imports `Mathlib.Analysis.Calculus.Deriv.Star`; its existing proof uses `deriv_conj_conj`.
- Independent `Challenge` and `Solution` interfaces compare the fixed-sigma curve, uniform 39/17 bound, exact curve away from the boundary, and middle-range large-values estimate. Three mathematical definitions are compared as well.
- Four intentional specification holes occur only in `Challenge`; `Solution` does not import it. Literal statement probes are compiled in `VerificationStatements` and retained among all 15 kernel-replay roots.

Independent AI source review has checked the enumerated transformations, file split, interface definitions and theorem quantifiers. This does not replace compilation, kernel checking, or human review. No mathematical theorem change is intended.

## Proposed metadata

`lean/formalization.yaml` retains the approved abstract body verbatim. The author, license text and original-contribution AGPL-3.0-only grant remain unchanged. Upstream licenses remain in force.

Before public action, review the proposed responsible-maintainer designation, `math.NT` classification, source-based origin and source descriptions, and legacy detector spelling `AGPL-3.0`. That spelling does not grant a later-version option; the detector match is a remaining preflight check.

## Remaining public actions

After private checks and review of the concrete candidate: publish the approved migration commit, then dispatch the prepared manual-only `.github/workflows/palomar-preflight.yml` to run the pinned official full hosted preflight against that exact commit with `project_path: lean`, Comparator path `lean/comparator.json`, and metadata path `lean/formalization.yaml`. Submission/intake is a separate authorized action. Registration requires a later explicit decision after the actual review is shown, bound to that review's SHA-256. No publication, workflow dispatch, intake, or registration was performed during this migration.
