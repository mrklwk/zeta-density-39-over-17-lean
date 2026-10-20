module
public import GeneralAdjacentInterpolation

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Unrestricted adjacent-moment rational second moment. Only the fixed
moment K, loss eta and fixed height dilation B precede the constant; there
is no lower bound on the ordinate-set cardinality. -/
theorem rational_energy_adjacent_unrestricted {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ : ℝ, 1 < T →
      ∀ H : ℕ, 1 ≤ H → (H:ℝ) ≤ B*T → ∀ A : Finset ℚ,
      (∀ q ∈ A, 0 < q ∧ q.den ≤ H ∧ |Real.log (q:ℝ)| ≤ 1) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ≤ C*T^η*((H:ℝ)*(W.card:ℝ)^2+
        (H:ℝ)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (H:ℝ)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
  classical
  have hδ : 0 < η/2 := by positivity
  choose C hC hb using (fun n : ℕ => rational_dual_moment (k:=n+1) (by omega) hδ)
  let J : ℕ := ⌈1/(η/2)⌉₊
  let D : ℝ := 1+C (K-1)+∑ n ∈ range (J+1), C n
  have hD : 1 ≤ D := by
    have hs : 0 ≤ ∑ n ∈ range (J+1), C n := sum_nonneg (fun n _ => (hC n).le)
    dsimp [D]
    linarith [hC (K-1)]
  have hDK : C (K-1) ≤ D := by
    have hs : 0 ≤ ∑ n ∈ range (J+1), C n := sum_nonneg (fun n _ => (hC n).le)
    dsimp [D]
    linarith
  have hDn (n : ℕ) (hn : n ≤ J) : C n ≤ D := by
    have hh := single_le_sum (s:=range (J+1)) (f:=C)
      (fun i _ => (hC i).le) (mem_range.mpr (by omega : n < J+1))
    dsimp [D]
    linarith [hC (K-1)]
  let F : ℝ := 3+2*D*B^(η/2)
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨F,hF,?_⟩
  intro T t₀ hT H hH hHT A hA W hW hsep
  have ht : 0 < T := by linarith
  have hh : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hr0 : (0:ℝ) ≤ W.card := Nat.cast_nonneg _
  have he0 : 0 ≤ rationalEnergy A W := sum_nonneg (fun _ _ => sq_nonneg _)
  have hTp : T^(η/2) ≤ T^η := Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
  have hF3 : 3 ≤ F := by
    have hs : 0 ≤ 2*D*B^(η/2) := by positivity
    dsimp [F]
    linarith
  have hFD : 2*D*B^(η/2) ≤ F := by dsimp [F]; linarith
  by_cases hs : (H:ℝ) ≤ T^(η/2)
  · have hcard : (A.card:ℝ) ≤ 3*(H:ℝ)*(H:ℝ) := by
      exact_mod_cast rational_card_le_height A H hA
    have hnonneg₁ : 0 ≤ (H:ℝ)^2*(W.card:ℝ)^(2-1/(K:ℝ)) := by positivity
    have hnonneg₂ : 0 ≤ (H:ℝ)*T^(1/(2*(K:ℝ)))*
        (W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) := by positivity
    calc
      _ ≤ (A.card:ℝ)*(W.card:ℝ)^2 := rational_energy_trivial A W
      _ ≤ (3*(H:ℝ)*(H:ℝ))*(W.card:ℝ)^2 := by gcongr
      _ ≤ (3*T^η*(H:ℝ))*(W.card:ℝ)^2 := by gcongr; exact hs.trans hTp
      _ = 3*T^η*((H:ℝ)*(W.card:ℝ)^2) := by ring
      _ ≤ F*T^η*((H:ℝ)*(W.card:ℝ)^2) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hnonneg₁,hnonneg₂]) (by positivity)
  · by_cases he : rationalEnergy A W = 0
    · rw [he]
      positivity
    have hep : 0 < rationalEnergy A W := lt_of_le_of_ne he0 (Ne.symm he)
    have hr1 : (1:ℝ) ≤ W.card := by
      by_cases hwe : W=∅
      · simp [hwe,rationalEnergy] at hep
      · exact_mod_cast (show 1 ≤ W.card from card_pos.mpr (nonempty_iff_ne_empty.mpr hwe))
    let Z : ℝ := D*(B*T)^(η/2)
    have hBT : 1 ≤ B*T := by nlinarith
    have hz : 1 ≤ Z := by
      have hp := Real.one_le_rpow hBT hδ.le
      dsimp [Z]
      nlinarith
    have hzp : 0 < Z := by linarith
    let U := rationalEnergy A W/Z
    have hup : 0 < U := div_pos hep hzp
    have hscaled (k : ℕ) (hk : 1 ≤ k) (hc : C (k-1) ≤ D) :
        U^k ≤ (T+(H:ℝ)^(2*k))*(W.card:ℝ)^(2*k-1) := by
      have hm := hb (k-1) H hH T t₀ ht.le A hA W hW hsep
      rw [Nat.sub_add_cancel hk] at hm
      apply adjacent_scaled_dual hk hep.le hr0 ht.le hh.le hz (hC (k-1)).le _ hm
      exact mul_le_mul hc (Real.rpow_le_rpow hh.le hHT hδ.le)
        (Real.rpow_nonneg hh.le _) (by linarith)
    have hu : U ≤ 2*((H:ℝ)*(W.card:ℝ)^2+
        (H:ℝ)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
        (H:ℝ)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
      by_cases hhigh : T ≤ (H:ℝ)^(2*K)
      · have hm : U^K ≤ 2*(H:ℝ)^(2*K)*(W.card:ℝ)^(2*K-1) :=
          (hscaled K hK hDK).trans (by gcongr; linarith)
        have hh' := adjacent_high_moment hK hup hh (by linarith : 0 < (W.card:ℝ)) hm
        have h0 : 0 ≤ (H:ℝ)*(W.card:ℝ)^2 := by positivity
        have h1 : 0 ≤ (H:ℝ)*T^(1/(2*(K:ℝ)))*
            (W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) := by positivity
        linarith only [hh',h0,h1]
      · let m : ℝ := Real.log H/Real.log T
        have hlog : 0 < Real.log T := Real.log_pos hT
        have hHm : T^m=(H:ℝ) := rpow_log_quotient hT hh
        have hδm : η/2 ≤ m := by
          have hl := Real.log_le_log (Real.rpow_pos_of_pos ht _) (le_of_not_ge hs)
          rw [Real.log_rpow ht] at hl
          exact (le_div_iff₀ hlog).mpr hl
        have hkp : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
        have hpow (n : ℕ) : (H:ℝ)^n=T^((n:ℝ)*m) := by
          rw [← hHm,adjacent_rpow_nat ht.le]
          congr 1
          ring
        have hm : m ≤ 1/(2*(K:ℝ)) := by
          have hp : T^((2*(K:ℝ))*m) ≤ T^(1:ℝ) := by
            rw [Real.rpow_one]
            convert (le_of_not_ge hhigh) using 1
            rw [hpow]
            norm_num
          have hx := (Real.rpow_le_rpow_left_iff hT).mp hp
          exact (le_div_iff₀ (by positivity : 0 < 2*(K:ℝ))).mpr (by nlinarith only [hx])
        obtain ⟨j,hKj,hjJ,hlo,hhi⟩ := adjacent_finite_height_cover hK hδ hδm hm
        have hj : 1 ≤ j := hK.trans hKj
        have hlop : (H:ℝ)^(2*j) ≤ T := by
          rw [hpow]
          calc
            _ ≤ T^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT.le (by
              norm_num only [Nat.cast_mul,Nat.cast_ofNat]
              exact hlo)
            _ = T := Real.rpow_one T
        have hhip : T ≤ (H:ℝ)^(2*(j+1)) := by
          rw [hpow]
          calc
            T = T^(1:ℝ) := (Real.rpow_one T).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT.le (by
              norm_num only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
              exact hhi)
        have hm₁ : U^j ≤ 2*T*(W.card:ℝ)^(2*j-1) :=
          (hscaled j hj (hDn (j-1) (by omega))).trans (by gcongr; linarith)
        have hm₂ : U^(j+1) ≤ 2*(H:ℝ)^(2*(j+1))*(W.card:ℝ)^(2*j+1) := by
          have hb' := (hscaled (j+1) (by omega) (by simpa using hDn j hjJ)).trans
            (show (T+(H:ℝ)^(2*(j+1)))*(W.card:ℝ)^(2*(j+1)-1) ≤
              2*(H:ℝ)^(2*(j+1))*(W.card:ℝ)^(2*(j+1)-1) by gcongr; linarith)
          simpa only [show 2*(j+1)-1=2*j+1 by omega] using hb'
        have hh' := adjacent_pair_envelope hK hKj hup ht hh hr1 hm₁ hm₂
        have h0 : 0 ≤ (H:ℝ)^2*(W.card:ℝ)^(2-1/(K:ℝ)) := by positivity
        linarith only [hh',h0]
    have hh' := (div_le_iff₀ hzp).mp hu
    have hzexpr : Z=(D*B^(η/2))*T^(η/2) := by
      dsimp [Z]
      rw [Real.mul_rpow (by linarith : 0 ≤ B) ht.le]
      ring
    rw [hzexpr] at hh'
    calc
      _ ≤ (2*D*B^(η/2))*T^(η/2)*((H:ℝ)*(W.card:ℝ)^2+
          (H:ℝ)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
          (H:ℝ)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
        convert hh' using 1; ring
      _ ≤ _ := by gcongr

end Montgomery.RationalMoment
