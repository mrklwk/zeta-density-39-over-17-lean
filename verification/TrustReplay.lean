/- Private release audit. Explicit public target roots, strict trust allowlist,
expected concrete dependencies and excluded obsolete premise consumers.
This harness is not imported by any mathematical theorem. -/
import GuthMaynard.Improvement.CurveBoundaryAudit
import GuthMaynard.Improvement.MiddleLargeValues
import Lean.Replay

open scoped BigOperators
set_option autoImplicit false
noncomputable section

/-- Literal statement check: a finite set containing exactly the actual zeros,
raw mathlib zeta and analytic multiplicity, and the fully expanded exponent. -/
theorem literal_combined_curve (σ ε : ℝ) (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1)
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ):ℝ) ≤
        C*T^((if σ ≤ 9/13 then 3*(1-σ)/(2-σ)
          else if σ ≤ 5/7 then 18*(1-σ)/(7*σ+3)
          else if σ ≤ 3/4 then (9/4)*(1-σ) else 3*(1-σ)/(2*σ))+ε) := by
  obtain ⟨C,hC,h⟩ := GuthMaynard.Improvement.combined_density_curve hσ hσ' hε
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F = MathCollab.Density.zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,MathCollab.Density.mem_zetaDensityFinset]
    simp only [MathCollab.Density.IsNontrivialZetaZero, and_assoc]
  simpa only [he,MathCollab.Density.zetaDensityCount,MathCollab.Density.zetaSlabCount,
    MathCollab.Density.zetaMultiplicity,GuthMaynard.Improvement.combinedDensityExponent] using h T hT

#print axioms literal_combined_curve

/-- Explicit uniformity domain, including the epsilon/delta order. -/
theorem literal_uniform_away_boundary (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 →
      (σ ≤ 3/4 ∨ 3/4+δ ≤ σ) → 2 ≤ T →
      (MathCollab.Density.zetaDensityCount σ T:ℝ) ≤
        C*T^((if σ ≤ 9/13 then 3*(1-σ)/(2-σ)
          else if σ ≤ 5/7 then 18*(1-σ)/(7*σ+3)
          else if σ ≤ 3/4 then (9/4)*(1-σ) else 3*(1-σ)/(2*σ))+ε) := by
  exact GuthMaynard.Improvement.combined_density_curve_uniform_away_boundary hδ hε

#print axioms literal_uniform_away_boundary

set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array Name := #[``GuthMaynard.Improvement.global_density_uniform,
    ``GuthMaynard.Improvement.middle_range_large_values,
    ``GuthMaynard.Improvement.full_density_curve,
    ``GuthMaynard.Improvement.combined_density_curve,
    ``GuthMaynard.Improvement.full_density_curve_uniform_left,
    ``GuthMaynard.Improvement.combined_density_curve_uniform_away_boundary,
    ``GuthMaynard.Improvement.combined_density_curve_endpoints,
    ``GuthMaynard.Improvement.combined_curve_boundary_modulus_obstruction,
    ``MathCollab.Density.Stronger.stronger_density_bound_native,
    ``literal_combined_curve, ``literal_uniform_away_boundary]
  let theoremCount : Nat := roots.size
  let mut pending := roots
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if declarations.contains name then
      continue
    let some ci := env.find? name | throwError "Missing proof dependency {name}"
    if ci.isUnsafe || ci.isPartial then
      throwError "Unsafe or partial declaration in mathematical closure: {name}"
    declarations := declarations.insert name ci
    for dependency in ci.getUsedConstantsAsSet do
      pending := pending.push dependency
    match ci with
    | .inductInfo info =>
      for other in info.all do
        pending := pending.push other
      for ctor in info.ctors do
        pending := pending.push ctor
    | .quotInfo _ => pending := pending.push ``Eq
    | _ => pure ()
  for n in ["GuthMaynard.Improvement.ShortMobiusFourthMoment",
      "GuthMaynard.Improvement.GuthMaynardUpperDensity",
      "GuthMaynard.Improvement.global_density_uniform_of_inputs",
      "GuthMaynard.Improvement.global_density_uniform_of_moment_ingham"] do
    if declarations.contains n.toName then
      throwError "Eliminated premise or obsolete consumer remains reachable: {n}"
  for n in ["MathCollab.Density.Stronger.zeta_twelfth_physical_native",
      "MathCollab.Density.Stronger.Atkinson.localMeanStationaryInput_native",
      "MathCollab.Density.Stronger.PointMean.pointMeanInput_native",
      "riemannZeta", "analyticOrderNatAt",
      "MathCollab.Density.zetaDensityCount", "MathCollab.Density.zetaSlabCount",
      "GuthMaynard.Improvement.weak_short_moment",
      "GuthMaynard.Improvement.ingham_lower_density",
      "MathCollab.Density.zeta_density_bound",
      "MathCollab.Density.Stronger.Fourth.zeta_fourth_dyadic"] do
    unless declarations.contains n.toName do
      throwError "Expected concrete dependency missing: {n}"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : Array Name := #[]
  for (name, ci) in declarations.toList do
    if ci.isAxiom then
      unless allowed.contains name do
        throwError "Unexpected axiom in proof closure: {name}"
      axioms := axioms.push name
  logInfo m!"Proof closure: {declarations.size} declarations; {roots.size} project roots; {theoremCount} theorem roots. Axioms: {axioms}"
  let names := (declarations.toList.map (fun (n, _) => n.toString)).mergeSort
  liftIO <| IO.FS.createDirAll "."
  liftIO <| IO.FS.writeFile "target-proof-dependencies.txt"
    (String.intercalate "\n" names ++ "\n")
  let fresh ← mkEmptyEnvironment
  let checked ← fresh.toKernelEnv.replay declarations
  for root in roots do
    unless (checked.find? root).isSome do
      throwError "Replay omitted root {root}"
  logInfo m!"FRESH PROOF CLOSURE REPLAY PASS: {declarations.size} declarations, {roots.size} roots, {theoremCount} theorem roots."
