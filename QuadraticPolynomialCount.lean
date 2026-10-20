module
public import QuadraticHeightBudget

@[expose] public section

open Filter Finset
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- Full perturbed detecting-length window for the actual bounded polynomial.
This theorem is unconditional; coefficient-one zero detection is a separate
remaining analytic step. -/
theorem quadratic_polynomial_count_loss {σ a δ : ℝ}
    (hw : QuadraticWindow σ a) (hδ : 0 < δ)
    (hδ' : δ ≤ (1-3*a/2)/2) (hsmall : 9*δ < a*(4*σ-3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ N t₀ : ℝ, T^a ≤ N → N ≤ T^(3*a/2+δ) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+51*δ) := by
  obtain ⟨A,hA,hbound⟩ := finite_quadratic_large_value_second MathCollab.Density.comparisonCutoff hδ
  refine ⟨1+(1+6*A)^3,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),quadratic_diagonal_budget hw hA hδ.le hsmall]
    with T hT hsink
  intro N t₀ hlo hhi b hb W hW hsep hlarge
  have hTp : 0 < T := by linarith
  have hN1 : 1 ≤ N := (Real.one_le_rpow hT.le (show 0 ≤ a by linarith [hw.a_low])).trans hlo
  have hNp : 0 < N := by linarith
  have hV : 0 < N^σ*T^(-2*δ) := by positivity
  let p := 3*a*(1-σ)
  have hP : 0 < T^p := by positivity
  obtain ⟨L,hNL,hLT,hbase,hfirst,hsecond⟩ := quadratic_monomial_budgets hw hδ.le hδ' hT hNp hlo hhi
  have hLp : 0 < L := hNp.trans_le hNL
  by_cases hR : (W.card:ℝ) ≤ T^p
  · have hp : T^p ≤ T^(p+51*δ) := Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
    exact (hR.trans hp).trans (by
      have hC : 1 ≤ 1+(1+6*A)^3 := by
        have hh : 0 ≤ (1+6*A)^3 := by positivity
        linarith only [hh]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ T^(p+51*δ)))
  · have hs : T^p ≤ (W.card:ℝ) := (le_of_not_ge hR)
    have hquad := hbound T t₀ N L hT hN1 hNL hLT b hb W (N^σ*T^(-2*δ)) hV.le hW hlarge hsep
    have hh := quadratic_scalar_absorption hNp hLp hTp hV hP hs
      (Real.one_le_rpow hT.le (show 0 ≤ 16*δ by positivity))
      (Real.one_le_rpow hT.le hδ.le) hA hquad (hsink.2 N hNp hlo)
      hbase hfirst hsecond
    have he : (T^δ)^3*(T^(16*δ))^3*T^p=T^(p+51*δ) := by
      rw [← Real.rpow_natCast (T^δ) 3,← Real.rpow_mul hTp.le,
        ← Real.rpow_natCast (T^(16*δ)) 3,← Real.rpow_mul hTp.le,
        ← Real.rpow_add hTp,← Real.rpow_add hTp]
      congr 1
      norm_num
      ring
    calc
      _ ≤ (1+6*A)^3*(T^δ)^3*(T^(16*δ))^3*T^p := hh
      _ = (1+6*A)^3*T^(p+51*δ) := by rw [← he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- For every final epsilon, actual general polynomials have the pictured
count exponent throughout the exact full length window. -/
theorem quadratic_polynomial_count {σ a ε : ℝ}
    (hw : QuadraticWindow σ a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ N t₀ : ℝ, T^a ≤ N → N ≤ T^(3*a/2) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  let δ := min (ε/1000) (min ((1-3*a/2)/4) (a*(4*σ-3)/100))
  have ha : 0 < a := by linarith [hw.a_low]
  have hg : 0 < a*(4*σ-3) := mul_pos ha (by linarith [hw.sigma_low])
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min (by positivity) (lt_min (by linarith [hw.a_high]) (by positivity))
  have hδeps : δ ≤ ε/1000 := min_le_left _ _
  have hδa : δ ≤ (1-3*a/2)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδg : δ ≤ a*(4*σ-3)/100 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C,hC,hb⟩ := quadratic_polynomial_count_loss hw hδ (by linarith [hw.a_high]) (by linarith)
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),hb] with T hT hh
  intro N t₀ hlo hhi b hcoeff W hW hsep hlarge
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := (Real.rpow_pos_of_pos hTp _).trans_le hlo
  have hu : N ≤ T^(3*a/2+δ) := hhi.trans (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith))
  have hV : N^σ*T^(-2*δ) ≤ N^σ := by
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hT.le (show -2*δ ≤ 0 by linarith)
    exact mul_le_of_le_one_right (Real.rpow_nonneg hNp.le _) hp
  exact (hh N t₀ hlo hu b hcoeff W hW hsep (fun t ht => hV.trans (hlarge t ht))).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)) hC.le)

end Montgomery.RationalMoment
