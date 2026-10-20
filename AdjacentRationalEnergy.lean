module
public import AdjacentMomentEnvelope

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Normalize a proved dual moment by one common constant. -/
theorem adjacent_scaled_dual {S R T H Z C η : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (_hS : 0 ≤ S) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hH : 0 ≤ H) (hZ : 1 ≤ Z) (_hC : 0 ≤ C)
    (hc : C*H^η ≤ Z)
    (hm : S^k ≤ R^(2*k-1)*(C*(T+H^(2*k))*H^η)) :
    (S/Z)^k ≤ (T+H^(2*k))*R^(2*k-1) := by
  have hZ0 : 0 < Z := by linarith
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hZ0 k)).mpr
  have hz : Z ≤ Z^k := by simpa using pow_le_pow_right₀ hZ hk
  calc
    _ ≤ R^(2*k-1)*(C*(T+H^(2*k))*H^η) := hm
    _ = (C*H^η)*((T+H^(2*k))*R^(2*k-1)) := by ring
    _ ≤ Z^k*((T+H^(2*k))*R^(2*k-1)) := by gcongr; exact hc.trans hz
    _ = _ := by ring

/-- Actual rational-frequency second moment from moments 2,3,4, on the
cardinality range needed for the second pictured continuation. Its constant
precedes the height, origin, rational set and ordinate set. No moment input
is left as a premise. The range R^3<=T^2 is retained explicitly. -/
theorem rational_energy_adjacent_second {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ : ℝ), 1 < T →
      ∀ (H : ℕ), 1 ≤ H → (H:ℝ) ≤ 2*T → ∀ (A : Finset ℚ),
      (∀ q ∈ A, 0 < q ∧ q.den ≤ H ∧ |Real.log (q:ℝ)| ≤ 1) →
      ∀ (W : Finset ℝ), T^((5:ℝ)/9) ≤ W.card → (W.card:ℝ)^3 ≤ T^2 →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      rationalEnergy A W ≤ C*T^η*((H:ℝ)*(W.card:ℝ)^2+
        (H:ℝ)^2*(W.card:ℝ)^((3:ℝ)/2)+
        (H:ℝ)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by
  obtain ⟨C₀,hC₀,hs⟩ := rational_energy_interval_short_range
    (K:=4) (by norm_num) hη (B:=1) (by norm_num)
  obtain ⟨C₂,hC₂,hm₂⟩ := rational_dual_moment (k:=2) (by norm_num) hη
  obtain ⟨C₃,hC₃,hm₃⟩ := rational_dual_moment (k:=3) (by norm_num) hη
  obtain ⟨C₄,hC₄,hm₄⟩ := rational_dual_moment (k:=4) (by norm_num) hη
  let D : ℝ := 1+C₂+C₃+C₄
  have hD : 1 ≤ D := by dsimp [D]; linarith
  let C : ℝ := C₀+2*D*2^η
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro T t₀ hT H hH hHT A hA W hR hRT hW hsep
  have ht : 0 < T := by linarith
  have ht1 : 1 ≤ T := hT.le
  have hHr : (0:ℝ) ≤ H := Nat.cast_nonneg _
  have hRr : (0:ℝ) ≤ W.card := Nat.cast_nonneg _
  have hE : 0 ≤ rationalEnergy A W := sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : C₀ ≤ C := by
    have hh : 0 ≤ 2*D*2^η := by positivity
    dsimp [C]
    linarith
  have hC' : 2*D*2^η ≤ C := by dsimp [C]; linarith
  have hAf : ∀ q ∈ A, 0 < q ∧ (q.den:ℝ) ≤ 1*(H:ℝ) ∧ |Real.log (q:ℝ)| ≤ 1 := by
    intro q hq
    exact ⟨(hA q hq).1,by simpa using (show (q.den:ℝ) ≤ H by exact_mod_cast (hA q hq).2.1),(hA q hq).2.2⟩
  by_cases hshort : (H:ℝ)^4 ≤ W.card
  · have hh := hs T t₀ H hT hHr A hAf W (by norm_num; exact hR) hshort hW hsep
    exact hh.trans (by
      have hh0 : (H:ℝ)*(W.card:ℝ)^2 ≤
          (H:ℝ)*(W.card:ℝ)^2+(H:ℝ)^2*(W.card:ℝ)^((3:ℝ)/2)+
          (H:ℝ)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12) := by
        have h1 : 0 ≤ (H:ℝ)^2*(W.card:ℝ)^((3:ℝ)/2) := by positivity
        have h2 : 0 ≤ (H:ℝ)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12) := by positivity
        linarith
      calc
        C₀*T^η*(H:ℝ)*(W.card:ℝ)^2 = (C₀*T^η)*((H:ℝ)*(W.card:ℝ)^2) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hC (by positivity)) hh0
          (by positivity) (by positivity))
  · let Z : ℝ := D*(2*T)^η
    have hZ : 1 ≤ Z := by
      have hp := Real.one_le_rpow (show 1 ≤ 2*T by linarith) hη.le
      dsimp [Z]
      nlinarith
    have hZ0 : 0 < Z := by linarith
    have hc (B : ℝ) (hB : B ≤ D) (hB0 : 0 ≤ B) : B*(H:ℝ)^η ≤ Z := by
      dsimp [Z]
      exact mul_le_mul hB (Real.rpow_le_rpow hHr hHT hη.le)
        (Real.rpow_nonneg hHr _) (by linarith)
    have h2 := adjacent_scaled_dual (by norm_num : 1 ≤ (2:ℕ)) hE hRr ht.le hHr hZ
      hC₂.le (hc C₂ (by dsimp [D]; linarith) hC₂.le)
      (hm₂ H hH T t₀ ht.le A hA W hW hsep)
    have h3 := adjacent_scaled_dual (by norm_num : 1 ≤ (3:ℕ)) hE hRr ht.le hHr hZ
      hC₃.le (hc C₃ (by dsimp [D]; linarith) hC₃.le)
      (hm₃ H hH T t₀ ht.le A hA W hW hsep)
    have h4 := adjacent_scaled_dual (by norm_num : 1 ≤ (4:ℕ)) hE hRr ht.le hHr hZ
      hC₄.le (hc C₄ (by dsimp [D]; linarith) hC₄.le)
      (hm₄ H hH T t₀ ht.le A hA W hW hsep)
    norm_num at h2 h3 h4
    have hr2 : T ≤ (W.card:ℝ)^2 := by
      calc
        T = T^(1:ℝ) := (Real.rpow_one T).symm
        _ ≤ T^((5/9:ℝ)*2) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
        _ = (T^((5:ℝ)/9))^2 := by rw [adjacent_rpow_nat ht.le]; norm_num
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hR 2
    have h8 : T ≤ (H:ℝ)^8 := by
      have hh := pow_le_pow_left₀ hRr (le_of_not_ge hshort) 2
      exact hr2.trans (by convert hh using 1; ring)
    have hu := adjacent_moment_envelope (div_nonneg hE hZ0.le) ht.le hHr hRr h8 hRT h2 h3 h4
    have hb := (div_le_iff₀ hZ0).mp hu
    have hz : Z = (D*2^η)*T^η := by
      dsimp [Z]
      rw [Real.mul_rpow (by norm_num) ht.le]
      ring
    rw [hz] at hb
    calc
      _ ≤ (2*D*2^η)*T^η*((H:ℝ)^2*(W.card:ℝ)^((3:ℝ)/2)+
          (H:ℝ)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by convert hb using 1; ring
      _ ≤ _ := by
        have hh : (H:ℝ)^2*(W.card:ℝ)^((3:ℝ)/2)+
            (H:ℝ)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12) ≤
            (H:ℝ)*(W.card:ℝ)^2+(H:ℝ)^2*(W.card:ℝ)^((3:ℝ)/2)+
            (H:ℝ)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12) := by
          have hn : 0 ≤ (H:ℝ)*(W.card:ℝ)^2 := by positivity
          linarith
        gcongr

end Montgomery.RationalMoment
