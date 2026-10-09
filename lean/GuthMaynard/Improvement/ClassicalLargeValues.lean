import GuthMaynard.Improvement.SeparatedSecondMoment
import GuthMaynard.Improvement.RealIntegerSource
import GuthMaynard.Improvement.ReflectionNearRow
import MathCollab.Density.LargeValues
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
namespace GuthMaynard.Improvement

def classicalLargeValueBudget (N T V : ℝ) : ℝ := N^2/V^2+T*N^4/V^6

/-- The audited theorem's cross term is bounded by the classical two-term budget. -/
theorem classical_cross_budget {N T V : ℝ} (hN : 0 ≤ N) (hT : 0 ≤ T) (hV : 0 < V) :
    N^3*Real.sqrt T/V^4 ≤ classicalLargeValueBudget N T V := by
  have hs : (N^2*Real.sqrt T)^2=N^4*T := by rw [mul_pow,Real.sq_sqrt hT]; ring
  have hh := sq_nonneg (N*V^2-N^2*Real.sqrt T)
  unfold classicalLargeValueBudget
  apply (mul_le_mul_iff_left₀ (pow_pos hV 6)).mp
  have he : (N^2/V^2+T*N^4/V^6)*V^6=N^2*V^4+T*N^4 := by field_simp
  rw [he]
  have he' : (N^3*Real.sqrt T/V^4)*V^6=N^3*Real.sqrt T*V^2 := by field_simp
  rw [he']
  nlinarith [mul_nonneg (show 0 ≤ N^3*Real.sqrt T by positivity) (sq_nonneg V)]

/-- Exact half-threshold and real-to-integer losses in the old large-values bound. -/
theorem classical_old_budget {M N T V : ℝ} (hM : 0 ≤ M) (hMN : M ≤ N)
    (hT : 0 ≤ T) (hV : 0 < V) :
    M^2/(V/2)^2+M^3*Real.sqrt T/(V/2)^4 ≤ 20*classicalLargeValueBudget N T V := by
  have hN : 0 ≤ N := hM.trans hMN
  have hA : 0 ≤ N^2/V^2 := by positivity
  have hB : 0 ≤ T*N^4/V^6 := by positivity
  have hc := classical_cross_budget hN hT hV
  calc
    _ ≤ N^2/(V/2)^2+N^3*Real.sqrt T/(V/2)^4 := by gcongr
    _ = 4*(N^2/V^2)+16*(N^3*Real.sqrt T/V^4) := by field_simp; ring
    _ ≤ _ := by unfold classicalLargeValueBudget at *; nlinarith

/-- For N>=8, the stronger interval range N<=T<=N² meets the audited integer scale condition. -/
theorem classical_floor_scale {N T : ℝ} (hN : 8 ≤ N) (hNT : N ≤ T) (hTN : T ≤ N^2) :
    T^(1/3:ℝ) ≤ (⌊N⌋₊:ℝ) ∧ (⌊N⌋₊:ℝ) ≤ T := by
  obtain ⟨hM,hlo,hhi⟩ := source_floor_bounds (show 2 ≤ N by linarith)
  have hm0 : (0:ℝ) ≤ ⌊N⌋₊ := by positivity
  have ht0 : 0 ≤ T := by linarith
  have hcube : T ≤ (⌊N⌋₊:ℝ)^3 := by
    have hh : N^2 ≤ (N/2)^3 := by nlinarith [mul_nonneg (show 0 ≤ N-8 by linarith) (sq_nonneg N)]
    exact hTN.trans (hh.trans (by gcongr))
  have hh := Real.rpow_le_rpow ht0 hcube (by norm_num : (0:ℝ) ≤ 1/3)
  have he : ((⌊N⌋₊:ℝ)^3)^(1/3:ℝ)=(⌊N⌋₊:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hm0]
    norm_num
  exact ⟨he ▸ hh,hhi.trans hNT⟩

/-- Logarithmic loss absorbed by a fixed positive power. -/
theorem classical_log_budget {N δ : ℝ} (hN : 1 ≤ N) (hδ : 0 < δ) :
    Real.log (2*N) ≤ (Real.log 2+1/δ)*N^δ := by
  have hn : 0 < N := by linarith
  rw [Real.log_mul (by norm_num) hn.ne']
  have hlog := Real.log_le_rpow_div hn.le hδ
  have hpow : 1 ≤ N^δ := Real.one_le_rpow hN hδ.le
  have hm := mul_le_mul_of_nonneg_left hpow (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have he : N^δ/δ=(1/δ)*N^δ := by ring
  rw [he] at hlog
  nlinarith

/-- Low-height scalar closure of the actual separated second moment. -/
theorem classical_low_scalar {ε N T V R : ℝ} (hε : 0 < ε) (hN : 2 ≤ N)
    (hT : 0 ≤ T) (hV : 0 < V) (_hR : 0 ≤ R)
    (hmoment : R*V^2 ≤ 204*T*N*Real.log (2*N))
    (hlow : V ≤ 16*N^(3/4+ε/8:ℝ)) :
    R ≤ (204*16^4*(Real.log 2+1/(ε/2)))*N^ε*classicalLargeValueBudget N T V := by
  have hN0 : 0 < N := by linarith
  have hv4 : V^4 ≤ 16^4*N^(3+ε/2:ℝ) := by
    have hh := pow_le_pow_left₀ hV.le hlow 4
    have he : (N^(3/4+ε/8:ℝ))^4=N^(3+ε/2:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
      congr 1
      norm_num
      ring
    simpa only [mul_pow,he] using hh
  have hlog := classical_log_budget (show 1 ≤ N by linarith) (show 0 < ε/2 by linarith)
  have hlog0 : 0 ≤ Real.log (2*N) := Real.log_nonneg (by linarith)
  have hpow : N^(3+ε/2:ℝ)*N^(ε/2:ℝ)*N=N^ε*N^4 := by
    rw [← Real.rpow_add hN0,show (3+ε/2)+(ε/2)=ε+3 by ring,Real.rpow_add hN0,
      Real.rpow_ofNat]
    ring
  have hrv : R*V^6 ≤ (204*16^4*(Real.log 2+1/(ε/2)))*N^ε*T*N^4 := by
    calc
      _ = (R*V^2)*V^4 := by ring
      _ ≤ (204*T*N*Real.log (2*N))*(16^4*N^(3+ε/2:ℝ)) :=
        mul_le_mul hmoment hv4 (by positivity) (by positivity)
      _ ≤ (204*T*N*((Real.log 2+1/(ε/2))*N^(ε/2:ℝ)))*(16^4*N^(3+ε/2:ℝ)) := by gcongr
      _ = _ := by
        have he := congrArg (fun x => (204*16^4*(Real.log 2+1/(ε/2)))*T*x) hpow
        nlinarith [he]
  have hC : 0 ≤ (204*16^4*(Real.log 2+1/(ε/2)))*N^ε := by positivity
  have hh := (le_div_iff₀ (pow_pos hV 6)).mpr hrv
  calc
    R ≤ (204*16^4*(Real.log 2+1/(ε/2)))*N^ε*(T*N^4/V^6) := by convert hh using 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hC


/-- Actual classical (Huxley-form) large values for real source length.
The audited integer theorem and actual separated second moment discharge both height ranges. -/
theorem classical_large_values {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T V t₀ : ℝ, 2 ≤ N → N ≤ T → T ≤ N^2 → 0 < V →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t ∈ Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*N^ε*(N^2/V^2+T*N^4/V^6) := by
  obtain ⟨C₁,hC₁,hold⟩ := MathCollab.Density.large_values
    (κ := ε/8) (ε := ε/2) (by positivity) (by positivity)
  let C₀ := 204*16^4*(Real.log 2+1/(ε/2))
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀+20*C₁,by positivity,?_⟩
  intro N T V t₀ hN hNT hTN hV a W ha hW hsep hlarge
  have hN0 : 0 < N := by linarith
  have hT : 0 ≤ T := by linarith
  have hb : 0 ≤ classicalLargeValueBudget N T V := by unfold classicalLargeValueBudget; positivity
  change (W.card:ℝ) ≤ (C₀+20*C₁)*N^ε*classicalLargeValueBudget N T V
  by_cases hne : W.Nonempty
  · by_cases hlow : V ≤ 16*N^(3/4+ε/8:ℝ)
    · have hmoment : (W.card:ℝ)*V^2 ≤ 204*T*N*Real.log (2*N) := by
        calc
          _ = ∑ _t ∈ W, V^2 := by simp
          _ ≤ ∑ t ∈ W, ‖boundedPolynomial N a t‖^2 :=
            sum_le_sum (fun t ht => (sq_le_sq₀ hV.le (norm_nonneg _)).mpr (hlarge t ht))
          _ ≤ _ := separated_second_moment_long hN hNT a ha W hW hsep
      have hh := classical_low_scalar hε hN hT hV (Nat.cast_nonneg W.card) hmoment hlow
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
          (Real.rpow_nonneg hN0.le _)) hb)
    · obtain ⟨t,ht⟩ := hne
      have hVupper := (hlarge t ht).trans (boundedPolynomial_norm_le_two_mul hN a ha t)
      have hpow : 1 ≤ N^(3/4+ε/8:ℝ) := Real.one_le_rpow (by linarith) (by positivity)
      have hV16 : 16 ≤ V := by linarith
      have hN8 : 8 ≤ N := by linarith
      obtain ⟨hM,hMlo,hMhi⟩ := source_floor_bounds hN
      obtain ⟨hscale₁,hscale₂⟩ := classical_floor_scale hN8 hNT hTN
      have hm0 : 0 < ⌊N⌋₊ := by omega
      have hheight : (⌊N⌋₊:ℝ)^(3/4+ε/8:ℝ) ≤ V/2 := by
        have hh := Real.rpow_le_rpow (Nat.cast_nonneg _) hMhi (show 0 ≤ (3/4+ε/8:ℝ) by positivity)
        linarith
      have hh := hold T (V/2) ⌊N⌋₊ a W (by linarith) hm0 (by positivity) hscale₁ hscale₂ hheight
        (source_floor_coefficients hN0.le a ha) ⟨t₀,hW⟩ hsep
        (fun s hs => detecting_floor_large_value hN (by linarith) a ha (hlarge s hs))
      have hTpow : T^(ε/2:ℝ) ≤ N^ε := by
        have hp := Real.rpow_le_rpow hT hTN (show 0 ≤ ε/2 by positivity)
        have he : (N^2)^(ε/2:ℝ)=N^ε := by
          rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
          congr 1
          ring
        exact hp.trans_eq he
      have hbudget := classical_old_budget (Nat.cast_nonneg ⌊N⌋₊) hMhi hT hV
      calc
        _ ≤ C₁*T^(ε/2:ℝ)*((⌊N⌋₊:ℝ)^2/(V/2)^2+(⌊N⌋₊:ℝ)^3*Real.sqrt T/(V/2)^4) := hh
        _ ≤ C₁*N^ε*(20*classicalLargeValueBudget N T V) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hTpow hC₁.le
          · exact hbudget
          · positivity
          · positivity
        _ = (20*C₁)*N^ε*classicalLargeValueBudget N T V := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀.le)
            (Real.rpow_nonneg hN0.le _)) hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    positivity

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.classical_cross_budget
#print axioms GuthMaynard.Improvement.classical_old_budget
#print axioms GuthMaynard.Improvement.classical_floor_scale
#print axioms GuthMaynard.Improvement.classical_log_budget
#print axioms GuthMaynard.Improvement.classical_low_scalar

#print axioms GuthMaynard.Improvement.classical_large_values
