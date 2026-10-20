module
public import FinalDensitySurface.Pieces
public import Lean

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let roots : Array Name := #[``FinalDensitySurface.provider_P1,``FinalDensitySurface.provider_P2,``FinalDensitySurface.provider_P3,``FinalDensitySurface.provider_P4,``FinalDensitySurface.provider_P5,``FinalDensitySurface.provider_P6,``FinalDensitySurface.provider_P7,``FinalDensitySurface.provider_P8,``FinalDensitySurface.provider_P9,``FinalDensitySurface.provider_P10,``FinalDensitySurface.provider_P11,``FinalDensitySurface.provider_P12,``FinalDensitySurface.provider_P13,``FinalDensitySurface.provider_P14,``FinalDensitySurface.provider_P15,``FinalDensitySurface.provider_P16,``FinalDensitySurface.provider_P17,``FinalDensitySurface.provider_P18,``FinalDensitySurface.provider_P19,``FinalDensitySurface.provider_P20,``FinalDensitySurface.provider_P21,``FinalDensitySurface.provider_P22,``FinalDensitySurface.provider_P23,``FinalDensitySurface.provider_P24,``FinalDensitySurface.provider_P25,``FinalDensitySurface.provider_P26,``FinalDensitySurface.provider_P27,``FinalDensitySurface.provider_P28,``FinalDensitySurface.provider_P29,``FinalDensitySurface.provider_P30,``FinalDensitySurface.provider_P31,``FinalDensitySurface.piece_G1,``FinalDensitySurface.piece_G2,``FinalDensitySurface.piece_G3,``FinalDensitySurface.piece_G4,``FinalDensitySurface.piece_G5,``FinalDensitySurface.piece_G6,``FinalDensitySurface.piece_G7,``FinalDensitySurface.piece_G8,``FinalDensitySurface.piece_G9,``FinalDensitySurface.piece_G10,``FinalDensitySurface.piece_B1,``FinalDensitySurface.piece_B2,``FinalDensitySurface.piece_B3,``FinalDensitySurface.piece_B4,``FinalDensitySurface.piece_B5,``FinalDensitySurface.piece_B6,``FinalDensitySurface.piece_O1,``FinalDensitySurface.piece_O2,``FinalDensitySurface.piece_O3,``FinalDensitySurface.piece_O4,``FinalDensitySurface.piece_O5,``FinalDensitySurface.piece_O6,``FinalDensitySurface.piece_O7,``FinalDensitySurface.piece_O8,``FinalDensitySurface.piece_O9,``FinalDensitySurface.piece_O10,``FinalDensitySurface.piece_O11,``FinalDensitySurface.piece_O12,``FinalDensitySurface.piece_O13,``FinalDensitySurface.piece_O14,``FinalDensitySurface.piece_O15,``FinalDensitySurface.piece_O16,``FinalDensitySurface.piece_O17,``FinalDensitySurface.piece_O18,``FinalDensitySurface.piece_O19,``FinalDensitySurface.piece_O20,``FinalDensitySurface.piece_O21,``FinalDensitySurface.piece_O22,``FinalDensitySurface.global39over17,``FinalDensitySurface.uniform_P29,``FinalDensitySurface.uniform_P30,``FinalDensitySurface.uniform_P31,``FinalDensitySurface.exact_zero_set_exists,``FinalDensitySurface.positive_finite_multiplicity,``FinalDensitySurface.exact_count_identity,``FinalDensitySurface.count_at_one]
  let env := (←getEnv).setExporting false
  let mut pending := roots
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if declarations.contains n then continue
    let some ci := env.find? n | throwError "Missing dependency {n}"
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial proof dependency {n}"
    if ci.isAxiom then
      unless [``Classical.choice,``propext,``Quot.sound].contains n do
        throwError "Forbidden axiom/admitted proof/computational axiom {n}"
    declarations := declarations.insert n ci
    for d in ci.getUsedConstantsAsSet do pending := pending.push d
    match ci with
    | .inductInfo info =>
      for other in info.all do pending := pending.push other
      for ctor in info.ctors do pending := pending.push ctor
    | .quotInfo _ => pending := pending.push ``Eq
    | _ => pure ()
  for n in #[``GuthMaynard.Improvement.global_density_uniform,``GuthMaynard.Improvement.short_density,``GuthMaynard.Improvement.upper_curve_density,``MathCollab.Density.Stronger.stronger_density_bound_native,``Montgomery.LiteratureDensity.source_extra_baseline_full_hb,``Montgomery.LiteratureDensity.source_extra_baseline_kerr6,``Montgomery.LiteratureDensity.source_extra_baseline_tty_1,``Montgomery.LiteratureDensity.source_extra_baseline_tty_2,``Montgomery.LiteratureDensity.source_extra_baseline_tty_3,``Montgomery.LiteratureDensity.source_extra_baseline_tty_4,``Montgomery.LiteratureDensity.source_extra_baseline_tty_5,``Montgomery.LiteratureDensity.source_extra_baseline_tty_6,``Montgomery.LiteratureDensity.source_extra_baseline_tty_7,``Montgomery.LiteratureDensity.source_extra_baseline_tty_8,``Montgomery.MonotoneCurve.seven_eighths_right_uniform,``Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3,``Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6,``Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7,``Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8,``Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4,``Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5,``Montgomery.RationalMoment.RightDetector.density_dashed_first,``Montgomery.RationalMoment.RightDetector.density_dashed_second,``Montgomery.RationalMoment.RightDetector.density_right_solid_fifth,``Montgomery.RationalMoment.RightDetector.density_right_solid_first,``Montgomery.RationalMoment.RightDetector.density_right_solid_fourth,``Montgomery.RationalMoment.RightDetector.density_right_solid_second,``Montgomery.RationalMoment.RightDetector.density_right_solid_third,``Montgomery.RationalMoment.adjacent_density_second,``Montgomery.RationalMoment.third_density_segment,``Montgomery.RationalMoment.two_term_density_first,``Montgomery.WrittenDensity.uniform_source_oct2_mixed_4,``Montgomery.WrittenDensity.uniform_source_oct2_mixed_5,``Montgomery.WrittenDensity.uniform_source_v7_A_1] do
    unless declarations.contains n do throwError "Literal surface omitted claimed backing theorem {n}"
  for n in #[``riemannZeta,``analyticOrderNatAt,``analyticOrderAt,
      ``MathCollab.Density.zetaDensityCount,``MathCollab.Density.zetaMultiplicity_pos,
      ``MathCollab.Density.zeta_analyticOrder_ne_top,``MathCollab.Density.zetaZeroRegion_finite,
      ``MathCollab.Density.mem_zetaDensityFinset,
      ``Montgomery.ZeroFreeHatching.actual_density_count_zero,
      ``OAI.SevenEighths.ProbeFinalAssemblyUnconditional.zeta_nonzero] do
    unless declarations.contains n do throwError "Missing literal analytic/count/proved provider input {n}"
  let pointwise : Array Name := #[``FinalDensitySurface.provider_P1,``FinalDensitySurface.provider_P2,``FinalDensitySurface.provider_P3,``FinalDensitySurface.provider_P4,``FinalDensitySurface.provider_P5,``FinalDensitySurface.provider_P6,``FinalDensitySurface.provider_P7,``FinalDensitySurface.provider_P8,``FinalDensitySurface.provider_P9,``FinalDensitySurface.provider_P10,``FinalDensitySurface.provider_P11,``FinalDensitySurface.provider_P12,``FinalDensitySurface.provider_P13,``FinalDensitySurface.provider_P14,``FinalDensitySurface.provider_P15,``FinalDensitySurface.provider_P16,``FinalDensitySurface.provider_P17,``FinalDensitySurface.provider_P18,``FinalDensitySurface.provider_P19,``FinalDensitySurface.provider_P20,``FinalDensitySurface.provider_P21,``FinalDensitySurface.provider_P22,``FinalDensitySurface.provider_P23,``FinalDensitySurface.provider_P24,``FinalDensitySurface.provider_P25,``FinalDensitySurface.provider_P26,``FinalDensitySurface.provider_P27,``FinalDensitySurface.provider_P28,``FinalDensitySurface.provider_P29,``FinalDensitySurface.provider_P30,``FinalDensitySurface.provider_P31,``FinalDensitySurface.piece_G1,``FinalDensitySurface.piece_G2,``FinalDensitySurface.piece_G3,``FinalDensitySurface.piece_G4,``FinalDensitySurface.piece_G5,``FinalDensitySurface.piece_G6,``FinalDensitySurface.piece_G7,``FinalDensitySurface.piece_G8,``FinalDensitySurface.piece_G9,``FinalDensitySurface.piece_G10,``FinalDensitySurface.piece_B1,``FinalDensitySurface.piece_B2,``FinalDensitySurface.piece_B3,``FinalDensitySurface.piece_B4,``FinalDensitySurface.piece_B5,``FinalDensitySurface.piece_B6,``FinalDensitySurface.piece_O1,``FinalDensitySurface.piece_O2,``FinalDensitySurface.piece_O3,``FinalDensitySurface.piece_O4,``FinalDensitySurface.piece_O5,``FinalDensitySurface.piece_O6,``FinalDensitySurface.piece_O7,``FinalDensitySurface.piece_O8,``FinalDensitySurface.piece_O9,``FinalDensitySurface.piece_O10,``FinalDensitySurface.piece_O11,``FinalDensitySurface.piece_O12,``FinalDensitySurface.piece_O13,``FinalDensitySurface.piece_O14,``FinalDensitySurface.piece_O15,``FinalDensitySurface.piece_O16,``FinalDensitySurface.piece_O17,``FinalDensitySurface.piece_O18,``FinalDensitySurface.piece_O19,``FinalDensitySurface.piece_O20,``FinalDensitySurface.piece_O21,``FinalDensitySurface.piece_O22]
  let uniforms : Array Name := #[``FinalDensitySurface.global39over17,``FinalDensitySurface.uniform_P29,``FinalDensitySurface.uniform_P30,``FinalDensitySurface.uniform_P31]
  let mut types : String := ""
  for root in roots do
    let some ci := env.find? root | throwError "Missing surface root {root}"
    match ci with
    | .thmInfo _ => pure ()
    | _ => throwError "Advertised surface root is not a theorem {root}"
    if pointwise.contains root || uniforms.contains root then
      liftTermElabM do
        Meta.forallTelescope ci.type fun xs body => do
          let expected := if pointwise.contains root then 5 else 2
          unless xs.size == expected do throwError "Hidden parameter/typeclass/analytic hypothesis in {root}"
          let reals := if pointwise.contains root then 2 else 1
          for i in [:reals] do
            unless ← Meta.isDefEq (←Meta.inferType xs[i]!) (mkConst ``Real) do
              throwError "Wrong cutoff/epsilon scalar type {root}"
          for i in [reals:xs.size] do
            unless ← Meta.isProof xs[i]! do throwError "Hidden data/class parameter {root}"
          unless body.isAppOfArity ``Exists 2 do throwError "C not before all heights/enumerations {root}"
    let pp ← liftTermElabM <| Meta.ppExpr ci.type
    types := types ++ s!"{root}\n{pp}\n\n"
  let mut usedModules : Std.HashMap Name Nat := {}
  for (n,_) in declarations.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      usedModules := usedModules.insert m (usedModules[m]?.getD 0 + 1)
  liftIO <| IO.FS.writeFile "FINAL_ROOT_TYPES.txt" types
  liftIO <| IO.FS.writeFile "FINAL_PROOF_DEPENDENCIES.txt"
    (String.intercalate "\n" ((declarations.toList.map (fun (n,_)=>n.toString)).mergeSort) ++ "\n")
  liftIO <| IO.FS.writeFile "FINAL_USED_MODULES.json" (Json.pretty <| toJson
    (usedModules.toList.map fun (n,k) => Json.mkObj [("module",toJson n.toString),("used_declarations",toJson k)]))
  liftIO <| IO.FS.writeFile "STATIC_RESULT.json" (Json.pretty <| Json.mkObj [
    ("status",toJson "PASS_TYPE_AND_TRANSITIVE_AXIOM_INSPECTION_NOT_KERNEL_REPLAY"),
    ("roots",toJson roots.size),("pointwise_literal_rows",toJson pointwise.size),
    ("uniform_literal_rows",toJson uniforms.size),("declarations",toJson declarations.size),
    ("axioms",toJson (["Classical.choice","propext","Quot.sound"] : List String)),
    ("hidden_surface_parameters",toJson false),("all_backing_roots_used",toJson true)])
  logInfo "Final density surface type/dependency checks PASS; kernel replay not run by this module."
