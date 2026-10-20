module
public import AdjacentWindow

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement
open Finset
theorem adjacent_upper_large_values {σ a p α δ : ℝ}
    (hw : AdjacentWindow σ a p α) (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ H → 2 ≤ N → H^α ≤ N → N ≤ H^(3*a/2+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*H^(p+18*δ) := by
  let D : ℝ := Real.log 2+1/δ
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hδ)
  refine ⟨102*(1+D),by positivity,?_⟩
  intro H N t₀ b W hH hN hlo hhi hb hloc hsep hlarge
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hV : 0 < N^σ*H^(-2*δ) := by positivity
  have hsmall : N^δ ≤ H^(2*δ) := by
    calc
      _ ≤ (H^(3*a/2+δ))^δ := Real.rpow_le_rpow hN0.le hhi hδ.le
      _ = H^((3*a/2+δ)*δ) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH1 (by
        have hh := mul_nonneg hδ.le (show 0 ≤ 2-3*a/2-δ by linarith [hw.a_high])
        nlinarith only [hh])
  have hpos : N^(2-2*σ) ≤ H^(p+2*δ) := by
    calc
      _ ≤ (H^(3*a/2+δ))^(2-2*σ) := Real.rpow_le_rpow hN0.le hhi (by linarith [hw.sigma_high])
      _ = H^((3*a/2+δ)*(2-2*σ)) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH1 (by
        have hh := mul_nonneg (show 0 ≤ 2*σ by linarith [hw.sigma_low]) hδ.le
        nlinarith only [hw.p_identity,hh])
  have hmean1 : H*N^(1-2*σ) ≤ H^p := by
    calc
      _ ≤ H*(H^α)^(1-2*σ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith [hw.sigma_low])) hH0.le
      _ = H^(1+α*(1-2*σ)) := by
        rw [← Real.rpow_mul hH0.le]
        nth_rw 1 [← Real.rpow_one H]
        rw [← Real.rpow_add hH0]
      _ = _ := by rw [hw.mean_identity]
  obtain ⟨_hdiv2,_hdiv4,hdivM⟩ := short_density_height_budgets hH0 hN0 σ δ
  have hmean := separated_second_moment hN hH0.le b hb W hloc hsep
  have hcard : (W.card:ℝ)*(N^σ*H^(-2*δ))^2 ≤ 102*N*(H+N*Real.log (2*N)) := by
    calc
      _ = ∑ _t ∈ W, (N^σ*H^(-2*δ))^2 := by simp
      _ ≤ ∑ t ∈ W, ‖boundedPolynomial N b t‖^2 :=
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
  have hmean2 : N^(2-2*σ)*Real.log (2*N) ≤ D*H^(p+4*δ) := by
    calc
      _ ≤ H^(p+2*δ)*(D*H^(2*δ)) :=
        mul_le_mul hpos hlog (Real.log_nonneg (by linarith)) (by positivity)
      _ = D*(H^(p+2*δ)*H^(2*δ)) := by ring
      _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring
  have hmean1' : H*N^(1-2*σ) ≤ H^(p+4*δ) :=
    hmean1.trans (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
  have hsum : H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N) ≤
      (1+D)*H^(p+4*δ) := by nlinarith
  have hbudget : 102*((H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N))*H^(4*δ)) ≤
      (102*(1+D))*H^(p+18*δ) := by
    calc
      _ ≤ 102*(((1+D)*H^(p+4*δ))*H^(4*δ)) := by gcongr
      _ = (102*(1+D))*(H^(p+4*δ)*H^(4*δ)) := by ring
      _ = (102*(1+D))*H^(p+8*δ) := by
        rw [← Real.rpow_add hH0]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) (by positivity)
  exact hc.trans hbudget



end Montgomery.RationalMoment
