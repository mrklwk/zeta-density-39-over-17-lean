module
public import RightQuadraticParameters

@[expose] public section

open Filter Finset
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The exact five right-hand solid detecting-length exponents. -/
def rightSolidLengthExponent (σ : ℝ) : ℝ :=
  if σ ≤ 29359/37574 then 1/(11*σ-7)
  else if σ ≤ 1015/1294 then 4744/(14610*σ-3849)
  else if σ ≤ 353/447 then 6154/(19062*σ-5079)
  else if σ ≤ 467/586 then 3782/(11808*σ-3195)
  else 2168/(6846*σ-1893)

theorem right_solid_quadratic_window {σ : ℝ} (hl : 7/9 ≤ σ) (hr : σ ≤ 4/5) :
    QuadraticWindow σ (rightSolidLengthExponent σ) := by
  unfold rightSolidLengthExponent
  split_ifs with h₁ h₂ h₃ h₄
  · exact right_quadratic_window_first σ hl h₁
  · exact right_quadratic_window_second σ (by linarith) h₂
  · exact right_quadratic_window_third σ (by linarith) h₃
  · exact right_quadratic_window_fourth σ (by linarith) h₄
  · exact right_quadratic_window_fifth σ (by linarith) hr

/-- Compact heights are restored using the literal separation/cardinality
bound; the polynomial theorem now holds for every real T>=2. -/
theorem quadratic_polynomial_count_all {σ a ε : ℝ}
    (hw : QuadraticWindow σ a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ∀ N t₀ : ℝ, T^a ≤ N → N ≤ T^(3*a/2) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  obtain ⟨C,hC,hb⟩ := quadratic_polynomial_count hw hε
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hb
  refine ⟨C+|T₀|+2,by positivity,?_⟩
  intro T hT N t₀ hlo hhi b hcoeff W hW hsep hlarge
  have hTp : 0 < T := by linarith
  have hp : 0 ≤ 3*a*(1-σ)+ε := by
    have ha : 0 < a := by linarith [hw.a_low]
    have hh : 0 < 3*a*(1-σ) := mul_pos (mul_pos (by norm_num) ha) (by linarith [hw.sigma_high])
    linarith
  have hpow : 1 ≤ T^(3*a*(1-σ)+ε) := Real.one_le_rpow (by linarith) hp
  by_cases hbig : T₀ ≤ T
  · exact (hT₀ T hbig N t₀ hlo hhi b hcoeff W hW hsep hlarge).trans
      (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg T₀] : C ≤ C+|T₀|+2) (by positivity))
  · have hc := separated_interval_card hTp.le W hW hsep
    have hbound : (W.card:ℝ) ≤ C+|T₀|+2 := by linarith [le_abs_self T₀]
    exact hbound.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (show 0 ≤ C+|T₀|+2 by positivity))

/-- All five solid right-hand GENERAL-POLYNOMIAL bounds. The conclusion
counts large values of the literal polynomial, not zeta zeros. -/
theorem right_solid_polynomial_count {σ ε : ℝ}
    (hl : 7/9 ≤ σ) (hr : σ ≤ 4/5) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ∀ N t₀ : ℝ, T^(rightSolidLengthExponent σ) ≤ N →
      N ≤ T^(3*rightSolidLengthExponent σ/2) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*rightSolidLengthExponent σ*(1-σ)+ε) :=
  quadratic_polynomial_count_all (right_solid_quadratic_window hl hr) hε

end Montgomery.RationalMoment
