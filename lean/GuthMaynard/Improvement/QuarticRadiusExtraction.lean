import GuthMaynard.Improvement.QuarticExtraction
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- A subpower radius meets any fixed polynomial tail order after a uniform
bounded-height exception. This lemma is purely scalar. -/
theorem quartic_radius_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ℝ, 0 < ν ∧ ν ≤ ε/2 ∧ ν ≤ 1 ∧ ∃ q : ℕ, 5 ≤ ν*(q:ℝ) := by
  let ν := min (ε/2) (1/2:ℝ)
  have hν : 0 < ν := lt_min (by positivity) (by norm_num)
  obtain ⟨q,hq⟩ := exists_nat_ge (5/ν)
  refine ⟨ν,hν,min_le_left _ _,(min_le_right _ _).trans (by norm_num),q,?_⟩
  have hh := (div_le_iff₀ hν).mp hq
  nlinarith

/-- The only analytic hypothesis is the actual truncated fourth moment.
The radius and tail smallness have been discharged with uniform constants;
small N is handled by the audited packing estimate. -/
theorem quartic_extraction_of_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T U V M : ℝ,
      2 ≤ N → N ≤ T → T ≤ N^2 → 1 ≤ V → V ≤ U → U ≤ 2*N →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      MathCollab.Density.oneSeparated W → (∀ w ∈ W, w ∈ Icc (0:ℝ) T) →
      (∀ w ∈ W, V ≤ ‖boundedPolynomial N a w‖) →
      (∫ t, (sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T))
        (boundedPolynomial N a) U t)^2) ≤ M →
      (W.card:ℝ) ≤ C*N^ε*(N^2/U^2+T*N^4/U^6+M/V^4) := by
  obtain ⟨ν,hν,hνε,hν1,q,hq⟩ := quartic_radius_parameters hε
  obtain ⟨B,hB,hb⟩ := quartic_extraction (show 0 < ε/2 by positivity) q
  let N₀ := max 2 (2*B)
  let C := 8*N₀^2+2*B+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N T U V M hN hNT hTN hV hVU hUN a W ha hsep hw hv hM
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hV0 : 0 < V := by linarith
  have hU : 0 < U := hV0.trans_le hVU
  have hT : 0 < T := hN0.trans_le hNT
  have hm : 0 ≤ M := (integral_nonneg (fun t => sq_nonneg
    (sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U t))).trans hM
  have hp : 1 ≤ N^ε := Real.one_le_rpow hN1 hε.le
  have hx : 0 ≤ N^2/U^2+T*N^4/U^6 := by positivity
  have hy : 0 ≤ M/V^4 := by positivity
  by_cases hlarge : N₀ ≤ N
  · have hBN : 2*B ≤ N := (le_max_right _ _).trans hlarge
    let R := N^ν
    have hR : 0 < R := Real.rpow_pos_of_pos hN0 _
    have hR1 : 1 ≤ R := Real.one_le_rpow hN1 hν.le
    have hRT : R ≤ T := by
      apply le_trans _ hNT
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hν1
    have hpow : N^5 ≤ R^q := by
      have hh := Real.rpow_le_rpow_of_exponent_le hN1 hq
      simpa only [Real.rpow_mul hN0.le,Real.rpow_natCast,Real.rpow_ofNat] using hh
    have hsmall : B*N^4/R^q ≤ V^4/2 := by
      have hh : B*N^4/R^q ≤ 1/2 := by
        apply (div_le_iff₀ (pow_pos hR q)).mpr
        have hbN := mul_le_mul_of_nonneg_right hBN (pow_nonneg hN0.le 4)
        nlinarith
      have hv4 : (1:ℝ) ≤ V^4 := one_le_pow₀ hV
      linarith
    have he := hb N T R U V M hN hNT hTN hR hRT hU hV0 hsmall a W ha hsep hw hv hM
    have hrbudget : (R+1)*N^(ε/2) ≤ 2*N^ε := by
      calc
        _ ≤ (2*R)*N^(ε/2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 2*N^(ν+ε/2) := by rw [Real.rpow_add hN0]; ring
        _ ≤ 2*N^ε := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num)
    have hcoef : 2*B ≤ C := by dsimp [C]; nlinarith [sq_nonneg N₀]
    calc
      _ ≤ B*(2*N^ε*(N^2/U^2+T*N^4/U^6)+N^ε*(M/V^4)) := by
        apply he.trans
        apply mul_le_mul_of_nonneg_left _ hB.le
        apply add_le_add (mul_le_mul_of_nonneg_right hrbudget hx)
        exact le_mul_of_one_le_left hy hp
      _ ≤ (2*B)*N^ε*(N^2/U^2+T*N^4/U^6+M/V^4) := by
        have hh : 0 ≤ B*N^ε*(M/V^4) := by positivity
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (by positivity)) (add_nonneg hx hy)
  · have hNN : N ≤ N₀ := le_of_not_ge hlarge
    have hN₀ : 0 ≤ N₀ := hN0.le.trans hNN
    have hspan := MathCollab.Density.intervalSpan_le_of_forall hT.le (U := W) (by
      intro t ht s hs
      obtain ⟨ht0,htT⟩ := hw t ht
      obtain ⟨hs0,hsT⟩ := hw s hs
      exact abs_le.mpr ⟨by linarith,by linarith⟩)
    have hcard := MathCollab.Density.separated_card_le_localDiameter hsep
    unfold MathCollab.Density.localDiameter at hcard
    have hcount : (W.card:ℝ) ≤ 2*N₀^2 := by
      have hh := pow_le_pow_left₀ hN0.le hNN 2
      nlinarith
    have hquarter : 1/4 ≤ N^2/U^2 := by
      apply (le_div_iff₀ (pow_pos hU 2)).mpr
      have hh := pow_le_pow_left₀ hU.le hUN 2
      nlinarith
    have hbudget : 1/4 ≤ N^2/U^2+T*N^4/U^6+M/V^4 := by
      have hh : 0 ≤ T*N^4/U^6 := by positivity
      linarith
    have hcoef : 8*N₀^2 ≤ C := by dsimp [C]; linarith
    have hCpow : C ≤ C*N^ε := le_mul_of_one_le_right hC.le hp
    have hh := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ C*N^ε by positivity)
    nlinarith

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.quartic_radius_parameters
#print axioms GuthMaynard.Improvement.quartic_extraction_of_moment
