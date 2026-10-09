import GuthMaynard.Improvement.UpperCurveBudgets

open Finset Set
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Actual large values for sigma in [5/7,3/4]. The intermediate lengths
pad the observation time to N^(6/5), preserving the original threshold and
finite set. The middle theorem is invoked only within its proved range. -/
theorem upper_curve_large_values {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ H N t₀ : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
      5/7 ≤ σ → σ ≤ 3/4 → 2 ≤ H → 2 ≤ N →
      H^(3/4:ℝ) ≤ N → N ≤ H^(9/8+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*H^((9/4)*(1-σ)+10*δ) := by
  obtain ⟨C,hC,hmid⟩ := middle_range_large_values δ hδ
  let D : ℝ := Real.log 2+1/δ
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hδ)
  refine ⟨2*C+102*(1+D),by positivity,?_⟩
  intro σ H N t₀ a W hσ hσ' hH hN hlo hhi ha hloc hsep hlarge
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hV : 0 < N^σ*H^(-2*δ) := by positivity
  obtain ⟨hsmall,hpos⟩ := upper_curve_length_budgets hσ hσ' hH1 hN0.le hδ.le hδ' hhi
  obtain ⟨hdiv2,_hdiv4,hdivM⟩ := short_density_height_budgets hH0 hN0 σ δ
  have hp : 0 ≤ H^((9/4)*(1-σ)+10*δ) := by positivity
  by_cases hm : N ≤ H^(upperCurveSplit σ)
  · obtain ⟨S,htlo,hthi,hHS,hquartic⟩ := upper_curve_padded_time hσ hσ' hH1 hN hlo hm
    have hS0 : 0 < S := hH0.trans_le hHS
    have hlocS : ∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+S := by
      intro t ht
      exact ⟨(hloc t ht).1,by linarith [(hloc t ht).2]⟩
    have hc := hmid N S (N^σ*H^(-2*δ)) t₀ a W hN htlo hthi hV ha hlocS hsep hlarge
    rw [hdiv2,upper_window_padded_denominator hH0 hN0 S σ δ] at hc
    have hb2 : N^(2-2*σ)*H^(4*δ) ≤ H^((9/4)*(1-σ)+8*δ) := by
      calc
        _ ≤ H^((9/4)*(1-σ)+2*δ)*H^(4*δ) :=
          mul_le_mul_of_nonneg_right hpos (by positivity)
        _ = H^((9/4)*(1-σ)+6*δ) := by
          rw [← Real.rpow_add hH0]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    have hb4 : (N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ) ≤
        H^((9/4)*(1-σ)+8*δ) := by
      calc
        _ ≤ H^((9/4)*(1-σ))*H^(8*δ) :=
          mul_le_mul_of_nonneg_right hquartic (by positivity)
        _ = _ := (Real.rpow_add hH0 _ _).symm
    have hsum : N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ) ≤
        2*H^((9/4)*(1-σ)+8*δ) := by linarith
    have hbudget : C*N^δ*(N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ)) ≤
        (2*C)*H^((9/4)*(1-σ)+10*δ) := by
      calc
        _ ≤ (C*H^(2*δ))*(2*H^((9/4)*(1-σ)+8*δ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsmall hC.le) hsum (by positivity) (by positivity)
        _ = (2*C)*(H^(2*δ)*H^((9/4)*(1-σ)+8*δ)) := by ring
        _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring
    exact (hc.trans hbudget).trans
      (mul_le_mul_of_nonneg_right (by linarith : 2*C ≤ 2*C+102*(1+D)) hp)
  · have hmean := separated_second_moment hN hH0.le a ha W hloc hsep
    have hcard : (W.card:ℝ)*(N^σ*H^(-2*δ))^2 ≤ 102*N*(H+N*Real.log (2*N)) := by
      calc
        _ = ∑ _t ∈ W, (N^σ*H^(-2*δ))^2 := by simp
        _ ≤ ∑ t ∈ W, ‖boundedPolynomial N a t‖^2 :=
          sum_le_sum (fun t ht => pow_le_pow_left₀ hV.le (hlarge t ht) 2)
        _ ≤ _ := hmean
    have hc : (W.card:ℝ) ≤ 102*((H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N))*H^(4*δ)) := by
      have hh := (le_div_iff₀ (sq_pos_of_pos hV)).mpr hcard
      have he : 102*N*(H+N*Real.log (2*N))/(N^σ*H^(-2*δ))^2 =
          102*(N*(H+N*Real.log (2*N))/(N^σ*H^(-2*δ))^2) := by ring
      rw [he,hdivM] at hh
      exact hh
    have hlog : Real.log (2*N) ≤ D*H^(2*δ) :=
      (classical_log_budget (by linarith : 1 ≤ N) hδ).trans
        (mul_le_mul_of_nonneg_left hsmall hD.le)
    have hmean1 := upper_curve_mean_budget hσ hσ' hH1 (le_of_not_ge hm)
    have hmean2 : N^(2-2*σ)*Real.log (2*N) ≤ D*H^((9/4)*(1-σ)+4*δ) := by
      calc
        _ ≤ H^((9/4)*(1-σ)+2*δ)*(D*H^(2*δ)) :=
          mul_le_mul hpos hlog (Real.log_nonneg (by linarith)) (by positivity)
        _ = D*(H^((9/4)*(1-σ)+2*δ)*H^(2*δ)) := by ring
        _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring
    have hmean1' : H*N^(1-2*σ) ≤ H^((9/4)*(1-σ)+4*δ) :=
      hmean1.trans (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
    have hsum : H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N) ≤
        (1+D)*H^((9/4)*(1-σ)+4*δ) := by nlinarith
    have hbudget : 102*((H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N))*H^(4*δ)) ≤
        (102*(1+D))*H^((9/4)*(1-σ)+10*δ) := by
      calc
        _ ≤ 102*(((1+D)*H^((9/4)*(1-σ)+4*δ))*H^(4*δ)) := by gcongr
        _ = (102*(1+D))*(H^((9/4)*(1-σ)+4*δ)*H^(4*δ)) := by ring
        _ = (102*(1+D))*H^((9/4)*(1-σ)+8*δ) := by
          rw [← Real.rpow_add hH0]; congr 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) (by positivity)
    exact (hc.trans hbudget).trans
      (mul_le_mul_of_nonneg_right (by linarith : 102*(1+D) ≤ 2*C+102*(1+D)) hp)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.upper_curve_large_values
