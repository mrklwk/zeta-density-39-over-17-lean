module
public import AdjacentZeroDensity
public import DashedInitialActualDensity
public import GuthMaynard.Improvement.GlobalDensity
public import GuthMaynard.Improvement.UpperCurveDensity
public import GuthMaynard.Improvement.WeakShortDensity
public import LaterPairs.NativeSharpRow6
public import LaterPairs.NativeSharpRows78
public import LiteratureDensity.Bounds
public import MathCollab.Density.Stronger.NativeDensity
public import MonotoneCurve.ActualDensity
public import RightSolidActualDensity
public import ThirdZeroDensity
public import TraceAlternatives.NativeCubeRows34
public import TraceAlternatives.NativeUniversalRows45
public import TwoTermZeroDensity
public import WrittenDensity.Uniform

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace FinalDensitySurface
open MathCollab.Density

theorem exact_zero_set_exists (σ T : ℝ) : ∃ F : Finset ℂ,
    ∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
  refine ⟨zetaZeroFinset σ (-T) T, ?_⟩
  intro ρ
  rw [mem_zetaDensityFinset]
  simp only [IsNontrivialZetaZero, and_assoc]

theorem positive_finite_multiplicity {ρ : ℂ}
    (hz : _root_.riemannZeta ρ = 0) (hlo : 0 < ρ.re) (hhi : ρ.re < 1) :
    0 < analyticOrderNatAt _root_.riemannZeta ρ ∧
      analyticOrderAt _root_.riemannZeta ρ ≠ ⊤ := by
  have h : IsNontrivialZetaZero ρ := ⟨hz,hlo,hhi⟩
  exact ⟨zetaMultiplicity_pos h,zeta_analyticOrder_ne_top (nontrivialZetaZero_ne_one h)⟩

theorem exact_count_identity (σ T : ℝ) (F : Finset ℂ)
    (hF : ∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T) :
    zetaDensityCount σ T = (∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) := by
  have he : F = zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero, and_assoc]
  subst F
  rfl

/-- Independent literal full-count statement for provider P1. Constant may depend on sigma and epsilon. -/
theorem provider_P1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((-3/(σ - 2))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_tty_1 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P2. Constant may depend on sigma and epsilon. -/
theorem provider_P2 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ < (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_tty_2 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P3. Constant may depend on sigma and epsilon. -/
theorem provider_P3 {σ ε : ℝ} (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_tty_3 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P4. Constant may depend on sigma and epsilon. -/
theorem provider_P4 {σ ε : ℝ} (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_tty_4 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P5. Constant may depend on sigma and epsilon. -/
theorem provider_P5 {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ < (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_tty_5 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P6. Constant may depend on sigma and epsilon. -/
theorem provider_P6 {σ ε : ℝ} (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_tty_6 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P7. Constant may depend on sigma and epsilon. -/
theorem provider_P7 {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ < (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_tty_7 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P8. Constant may depend on sigma and epsilon. -/
theorem provider_P8 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (1867/2347 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_tty_8 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P9. Constant may depend on sigma and epsilon. -/
theorem provider_P9 {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(2*σ))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_kerr6 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P10. Constant may depend on sigma and epsilon. -/
theorem provider_P10 {σ ε : ℝ} (hlo : (7/10 : ℝ) < σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.LiteratureDensity.source_extra_baseline_full_hb hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P11. Constant may depend on sigma and epsilon. -/
theorem provider_P11 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((18/(7*σ+3))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := GuthMaynard.Improvement.short_density hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P12. Constant may depend on sigma and epsilon. -/
theorem provider_P12 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/4)*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  exact GuthMaynard.Improvement.upper_curve_density hlo hhi hε

/-- Independent literal full-count statement for provider P13. Constant may depend on sigma and epsilon. -/
theorem provider_P13 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (_hhi : σ < (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(2*σ))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  clear _hhi
  convert (MathCollab.Density.Stronger.stronger_density_bound_native hlo hε) using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P14. Constant may depend on sigma and epsilon. -/
theorem provider_P14 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(8*σ-3))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  by_cases h : σ ≤ (12/17 : ℝ)
  ·
    obtain ⟨C,hC,hb⟩ := Montgomery.WrittenDensity.uniform_source_v7_A_1 hε
    convert (show ∃ C : ℝ,0<C ∧ ∀ T : ℝ,2≤T → (zetaDensityCount σ T:ℝ)≤C*T^(_+ε) from ⟨C,hC,fun T hT => hb σ T hlo h hT⟩) using 1
    all_goals ring_nf
  ·
    have hbound := Montgomery.RationalMoment.two_term_density_first (by linarith) hhi hε
    try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
    convert hbound using 1
    all_goals ring_nf

/-- Independent literal full-count statement for provider P15. Constant may depend on sigma and epsilon. -/
theorem provider_P15 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((12/(9*σ-1))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.adjacent_density_second hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P16. Constant may depend on sigma and epsilon. -/
theorem provider_P16 {σ ε : ℝ} (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((255/(153*σ+7))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.third_density_segment hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P17. Constant may depend on sigma and epsilon. -/
theorem provider_P17 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(11*σ-7))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.density_right_solid_first hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P18. Constant may depend on sigma and epsilon. -/
theorem provider_P18 {σ ε : ℝ} (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.density_right_solid_second hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P19. Constant may depend on sigma and epsilon. -/
theorem provider_P19 {σ ε : ℝ} (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.density_right_solid_third hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P20. Constant may depend on sigma and epsilon. -/
theorem provider_P20 {σ ε : ℝ} (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.density_right_solid_fourth hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P21. Constant may depend on sigma and epsilon. -/
theorem provider_P21 {σ ε : ℝ} (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  by_cases h : σ ≤ (4/5 : ℝ)
  ·
    have hbound := Montgomery.RationalMoment.RightDetector.density_right_solid_fifth hlo h hε
    try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
    convert hbound using 1
    all_goals ring_nf
  ·
    have hbound := Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) hhi hε
    try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
    convert hbound using 1
    all_goals ring_nf

/-- Independent literal full-count statement for provider P22. Constant may depend on sigma and epsilon. -/
theorem provider_P22 {σ ε : ℝ} (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((566/(606*σ-173))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.density_dashed_second hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P23. Constant may depend on sigma and epsilon. -/
theorem provider_P23 {σ ε : ℝ} (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P24. Constant may depend on sigma and epsilon. -/
theorem provider_P24 {σ ε : ℝ} (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P25. Constant may depend on sigma and epsilon. -/
theorem provider_P25 {σ ε : ℝ} (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P26. Constant may depend on sigma and epsilon. -/
theorem provider_P26 {σ ε : ℝ} (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P27. Constant may depend on sigma and epsilon. -/
theorem provider_P27 {σ ε : ℝ} (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P28. Constant may depend on sigma and epsilon. -/
theorem provider_P28 {σ ε : ℝ} (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  have hbound := Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 hlo hhi hε
  try dsimp only [Montgomery.WrittenDensity.DensityBound] at hbound
  convert hbound using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P29. Constant may depend on sigma and epsilon. -/
theorem provider_P29 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (_hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ ((1086/5537) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  clear _hhi
  obtain ⟨C,hC,h⟩ := Montgomery.MonotoneCurve.seven_eighths_right_uniform hε
  exact ⟨C,hC,fun T hT => h σ hlo T hT⟩

/-- Independent literal full-count statement for provider P30. Constant may depend on sigma and epsilon. -/
theorem provider_P30 {σ ε : ℝ} (hlo : (19/22 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((24/(30*σ-11))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  obtain ⟨C,hC,h⟩ := Montgomery.WrittenDensity.uniform_source_oct2_mixed_4 hε
  convert (show ∃ C : ℝ,0<C ∧ ∀ T : ℝ,2≤T → (zetaDensityCount σ T:ℝ)≤C*T^(_+ε) from ⟨C,hC,fun T hT => h σ T hlo hhi hT⟩) using 1
  all_goals ring_nf

/-- Independent literal full-count statement for provider P31. Constant may depend on sigma and epsilon. -/
theorem provider_P31 {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(σ+3))*(1-σ)) + ε) := by
  apply Montgomery.WrittenDensity.density_literal
  dsimp only [Montgomery.WrittenDensity.DensityBound]
  obtain ⟨C,hC,h⟩ := Montgomery.WrittenDensity.uniform_source_oct2_mixed_5 hε
  convert (show ∃ C : ℝ,0<C ∧ ∀ T : ℝ,2≤T → (zetaDensityCount σ T:ℝ)≤C*T^(_+ε) from ⟨C,hC,fun T hT => h σ T hlo hhi hT⟩) using 1
  all_goals ring_nf

/-- The separately announced uniform global estimate, not an additional chart provider. -/
theorem global39over17 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (1/2 : ℝ) ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((39/17 : ℝ)*(1-σ)) + ε) := by
  obtain ⟨C,hC,h⟩ := GuthMaynard.Improvement.global_density_uniform hε
  refine ⟨C,hC,?_⟩
  intro σ T hlo hhi hT F hF
  rw [← exact_count_identity σ T F hF]
  exact h σ T hlo hhi hT

end FinalDensitySurface
