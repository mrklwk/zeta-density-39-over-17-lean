module
public import FinalDensitySurface.StaticChecks
public import Lean.Replay

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
  let fresh ← mkEmptyEnvironment
  let checked ← fresh.toKernelEnv.replay declarations
  for root in roots do
    unless (checked.find? root).isSome do throwError "Fresh kernel omitted advertised root {root}"
  let result := s!"FINAL DENSITY CHART EMPTY-KERNEL PASS: {roots.size} independent literal/semantic roots; {declarations.size} used declarations;31sourceproviders;38plottedpieces;global39/17;fixedsigma and explicituniformquantifiers;actualMathlibzeta/analyticmultiplicities/bothsigns/allrealT>=2;onlyClassical.choice,propext,Quot.sound;trust0."
  liftIO <| IO.FS.writeFile "final-density-kernel-replay.txt" (result++"\n")
  liftIO <| IO.FS.writeFile "KERNEL_RESULT.json" (Json.pretty <| Json.mkObj [
    ("status",toJson "EMPTY_KERNEL_PASS"),("roots",toJson roots.size),
    ("declarations",toJson declarations.size),("trust_level",toJson (0:Nat)),
    ("allowed_axioms",toJson (["Classical.choice","propext","Quot.sound"]:List String)),
    ("source_providers",toJson (31:Nat)),("plotted_pieces",toJson (38:Nat)),
    ("new_standalone_zero_free_check",toJson false),
    ("density_proof_dependencies_include_previously_checked_nonvanishing",toJson true)])
  logInfo m!"{result}"
