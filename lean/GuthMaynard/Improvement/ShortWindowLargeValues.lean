module
public import GuthMaynard.Improvement.ShortDensityHeight

@[expose] public section

open Finset Set
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Actual large values throughout the powered detector window. Constants are
uniform in sigma; the upper length buffer and normalized height loss are
charged explicitly. The middle theorem is used only in its exact range. -/
theorem short_window_large_values {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ H N t₀ : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
      9/13 ≤ σ → σ ≤ 5/7 → 2 ≤ H → 2 ≤ N →
      H^(shortDensityA σ) ≤ N → N ≤ H^(shortDensityB σ+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*H^(shortDensityExponent σ+10*δ) := by
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
  have hsmall := short_density_small_power hσ hσ' hH1 hN0.le hδ.le hδ' hhi
  have hpos := short_density_positive_budget hσ hσ' hH1 hN0.le hδ.le hhi
  obtain ⟨hdiv2,hdiv4,hdivM⟩ := short_density_height_budgets hH0 hN0 σ δ
  have hp : 0 ≤ H^(shortDensityExponent σ+10*δ) := by positivity
  by_cases hm : N ≤ H^(5/6:ℝ)
  · obtain ⟨htlo,hthi⟩ := short_density_middle_time hσ hσ' hH1 hN0 hlo hm
    have hc := hmid N H (N^σ*H^(-2*δ)) t₀ a W hN htlo hthi hV ha hloc hsep hlarge
    rw [hdiv2,hdiv4] at hc
    have hb2 : N^(2-2*σ)*H^(4*δ) ≤ H^(shortDensityExponent σ+8*δ) := by
      calc
        _ ≤ H^(shortDensityExponent σ+2*δ)*H^(4*δ) :=
          mul_le_mul_of_nonneg_right hpos (by positivity)
        _ = H^(shortDensityExponent σ+6*δ) := by
          rw [← Real.rpow_add hH0]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    have hb4 : (N^(18/7-4*σ)*H^(6/7:ℝ))*H^(8*δ) ≤
        H^(shortDensityExponent σ+8*δ) := by
      calc
        _ ≤ H^(shortDensityExponent σ)*H^(8*δ) :=
          mul_le_mul_of_nonneg_right (short_density_middle_budget hσ hH0 hlo) (by positivity)
        _ = _ := (Real.rpow_add hH0 _ _).symm
    have hsum : N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*H^(6/7:ℝ))*H^(8*δ) ≤
        2*H^(shortDensityExponent σ+8*δ) := by linarith
    have hbudget : C*N^δ*(N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*H^(6/7:ℝ))*H^(8*δ)) ≤
        (2*C)*H^(shortDensityExponent σ+10*δ) := by
      calc
        _ ≤ (C*H^(2*δ))*(2*H^(shortDensityExponent σ+8*δ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsmall hC.le) hsum (by positivity) (by positivity)
        _ = (2*C)*(H^(2*δ)*H^(shortDensityExponent σ+8*δ)) := by ring
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
    have hmean1 := short_density_mean_budget hσ hσ' hH1 (le_of_not_ge hm)
    have hmean2 : N^(2-2*σ)*Real.log (2*N) ≤ D*H^(shortDensityExponent σ+4*δ) := by
      calc
        _ ≤ H^(shortDensityExponent σ+2*δ)*(D*H^(2*δ)) :=
          mul_le_mul hpos hlog (Real.log_nonneg (by linarith)) (by positivity)
        _ = D*(H^(shortDensityExponent σ+2*δ)*H^(2*δ)) := by ring
        _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring
    have hmean1' : H*N^(1-2*σ) ≤ H^(shortDensityExponent σ+4*δ) :=
      hmean1.trans (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
    have hsum : H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N) ≤
        (1+D)*H^(shortDensityExponent σ+4*δ) := by nlinarith
    have hbudget : 102*((H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N))*H^(4*δ)) ≤
        (102*(1+D))*H^(shortDensityExponent σ+10*δ) := by
      calc
        _ ≤ 102*(((1+D)*H^(shortDensityExponent σ+4*δ))*H^(4*δ)) := by gcongr
        _ = (102*(1+D))*(H^(shortDensityExponent σ+4*δ)*H^(4*δ)) := by ring
        _ = (102*(1+D))*H^(shortDensityExponent σ+8*δ) := by
          rw [← Real.rpow_add hH0]; congr 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) (by positivity)
    exact (hc.trans hbudget).trans
      (mul_le_mul_of_nonneg_right (by linarith : 102*(1+D) ≤ 2*C+102*(1+D)) hp)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_window_large_values
