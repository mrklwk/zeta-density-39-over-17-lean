module
public import RetunedLongMultiplicity

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- The literal positive excess of the actual critical-line zeta norm. -/
def criticalExcess (v t : ℝ) : ℝ := max (zetaMomentCriticalNorm t-v) 0

theorem criticalExcess_nonneg (v t : ℝ) : 0 ≤ criticalExcess v t := le_max_right _ _

theorem criticalExcess_continuous (v : ℝ) : Continuous (criticalExcess v) :=
  (continuous_zetaMomentCriticalNorm.sub continuous_const).max continuous_const

theorem critical_norm_le_threshold_add_excess (v t : ℝ) :
    zetaMomentCriticalNorm t ≤ v+criticalExcess v t := by
  have h := le_max_left (zetaMomentCriticalNorm t-v) 0
  dsimp only [criticalExcess]
  linarith

theorem integrable_translated_critical_mean (u : ℝ) :
    Integrable (fun t : ℝ => momentDecay 128 (t-u)*zetaMomentCriticalNorm t) := by
  have hh := (integrable_weightedCriticalMean 128 (by norm_num) u).comp_sub_right u
  simpa [momentDecay,zetaMomentCriticalNorm,div_eq_mul_inv,mul_comm] using hh

theorem weightedCriticalMean_eq_translated (u : ℝ) :
    weightedCriticalMean 128 u =
      ∫ t : ℝ, momentDecay 128 (t-u)*zetaMomentCriticalNorm t := by
  unfold weightedCriticalMean
  have hh := integral_sub_right_eq_self (μ := volume)
    (f := fun t : ℝ => ‖riemannZeta ((1/2 : ℂ)+((u+t : ℝ):ℂ)*Complex.I)‖/(1+|t|)^128) u
  simpa [momentDecay,zetaMomentCriticalNorm,div_eq_mul_inv,mul_comm] using hh.symm

/-- Actual first-moment far tail, independent of any zeta moment theorem. -/
theorem weightedCriticalMean_tail_pointwise {T u t : ℝ}
    (hT : 1 ≤ T) (hu : u ∈ Icc T (2*T)) (ht : t ∉ Icc 0 (3*T)) :
    momentDecay 128 (t-u)*zetaMomentCriticalNorm t ≤
      12*T^(-125 : ℝ)*momentDecay 2 (t-u) := by
  obtain ⟨hgap,htnorm⟩ := physical_tail_geometry hT hu ht
  have hTp : 0 < T := by linarith
  have hz : zetaMomentCriticalNorm t ≤ 12*(1+|t-u|) := by
    have hh := zetaMomentCriticalNorm_le_linear t
    linarith
  have hpow : T^125 ≤ (1+|t-u|)^125 := pow_le_pow_left₀ hTp.le (by linarith) _
  calc
    _ = zetaMomentCriticalNorm t/(1+|t-u|)^128 := by unfold momentDecay; ring
    _ ≤ (12*(1+|t-u|))/(1+|t-u|)^128 :=
      div_le_div_of_nonneg_right hz (by positivity)
    _ = 12/((1+|t-u|)^125*(1+|t-u|)^2) := by field_simp
    _ ≤ 12/(T^125*(1+|t-u|)^2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by
      rw [Real.rpow_neg hTp.le,show (125:ℝ)=((125:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      unfold momentDecay
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

theorem weightedCriticalMean_physical_tail {T u : ℝ} (hT : 1 ≤ T)
    (hu : u ∈ Icc T (2*T)) :
    (∫ t in (Icc 0 (3*T))ᶜ, momentDecay 128 (t-u)*zetaMomentCriticalNorm t) ≤
      12*T^(-125 : ℝ)*Real.pi := by
  have hi := integrable_translated_critical_mean u
  have hw : Integrable (fun t : ℝ => momentDecay 2 (t-u)) :=
    (integrable_momentDecay (by norm_num : 2 ≤ 2)).comp_sub_right u
  let C : ℝ := 12*T^(-125 : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∫ t in (Icc 0 (3*T))ᶜ, C*momentDecay 2 (t-u) := by
      apply setIntegral_mono_on hi.integrableOn (hw.const_mul C).integrableOn measurableSet_Icc.compl
      intro t ht
      exact weightedCriticalMean_tail_pointwise hT hu ht
    _ ≤ ∫ t : ℝ, C*momentDecay 2 (t-u) :=
      setIntegral_le_integral (hw.const_mul C) (Eventually.of_forall (fun t =>
        mul_nonneg hC (momentDecay_pos 2 (t-u)).le))
    _ = C*∫ t : ℝ, momentDecay 2 t := by
      rw [integral_const_mul,integral_sub_right_eq_self]
    _ ≤ C*Real.pi := mul_le_mul_of_nonneg_left (momentDecay_mass_bounds (by norm_num : 2 ≤ 2)).2 hC

/-- A literal truncation of each actual weighted zeta mean. -/
theorem weightedCriticalMean_le_threshold_excess {T u v : ℝ}
    (hT : 1 ≤ T) (hu : u ∈ Icc T (2*T)) (hv : 0 ≤ v) :
    weightedCriticalMean 128 u ≤ Real.pi*v+
      (∫ t in Icc 0 (3*T),momentDecay 128 (t-u)*criticalExcess v t)+
        12*T^(-125 : ℝ)*Real.pi := by
  have hw : Integrable (fun t : ℝ => momentDecay 128 (t-u)) :=
    (integrable_momentDecay (by norm_num : 2 ≤ 128)).comp_sub_right u
  have he : IntegrableOn (criticalExcess v) (Icc 0 (3*T)) :=
    (criticalExcess_continuous v).continuousOn.integrableOn_compact isCompact_Icc
  have hew : IntegrableOn (fun t => momentDecay 128 (t-u)*criticalExcess v t) (Icc 0 (3*T)) :=
    integrable_momentDecay_mul he 128 u
  have hi := integrable_translated_critical_mean u
  have hb : (∫ t in Icc 0 (3*T),momentDecay 128 (t-u)*zetaMomentCriticalNorm t) ≤
      Real.pi*v+(∫ t in Icc 0 (3*T),momentDecay 128 (t-u)*criticalExcess v t) := by
    calc
      _ ≤ ∫ t in Icc 0 (3*T),momentDecay 128 (t-u)*v+
          momentDecay 128 (t-u)*criticalExcess v t := by
        apply setIntegral_mono_on hi.integrableOn ((hw.mul_const v).integrableOn.add hew) measurableSet_Icc
        intro t _
        have hh := mul_le_mul_of_nonneg_left (critical_norm_le_threshold_add_excess v t)
          (momentDecay_pos 128 (t-u)).le
        simpa only [Pi.add_apply,mul_add] using hh
      _ = (∫ t in Icc 0 (3*T),momentDecay 128 (t-u))*v+
          (∫ t in Icc 0 (3*T),momentDecay 128 (t-u)*criticalExcess v t) := by
        rw [integral_add (hw.mul_const v).integrableOn hew,integral_mul_const]
      _ ≤ Real.pi*v+_ := by
        have hm : (∫ t in Icc 0 (3*T),momentDecay 128 (t-u)) ≤ Real.pi := by
          apply (setIntegral_le_integral hw (Eventually.of_forall (fun t => (momentDecay_pos _ _).le))).trans
          rw [integral_sub_right_eq_self]
          exact (momentDecay_mass_bounds (by norm_num : 2 ≤ 128)).2
        exact add_le_add (mul_le_mul_of_nonneg_right hm hv) le_rfl
  rw [weightedCriticalMean_eq_translated,
    ← integral_add_compl measurableSet_Icc hi]
  exact (add_le_add hb (weightedCriticalMean_physical_tail hT hu)).trans_eq (by ring)

/-- Unconditional separated sampling reduction to the literal positive excess
of actual critical-line zeta values. No tail estimate is assumed. -/
theorem separated_weightedCriticalMean_excess_count {T B : ℝ}
    (hT : 1 ≤ T) (hB : 0 < B) (htail : 48*Real.pi*T^(-125 : ℝ) ≤ B)
    (U : Finset ℝ) (hU : oneSeparated U)
    (hslab : ∀ u ∈ U,u ∈ Icc T (2*T))
    (hmean : ∀ u ∈ U,B ≤ weightedCriticalMean 128 u) :
    (U.card:ℝ)*B ≤ 2*separationMass*
      ∫ t in Icc 0 (3*T),criticalExcess (B/(4*Real.pi)) t := by
  let v : ℝ := B/(4*Real.pi)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hvB : Real.pi*v=B/4 := by dsimp [v]; field_simp
  have he : IntegrableOn (criticalExcess v) (Icc 0 (3*T)) :=
    (criticalExcess_continuous v).continuousOn.integrableOn_compact isCompact_Icc
  have hp (u : ℝ) (hu : u ∈ U) : B/2 ≤
      ∫ t in Icc 0 (3*T),momentDecay 128 (t-u)*criticalExcess v t := by
    have hh := (hmean u hu).trans (weightedCriticalMean_le_threshold_excess hT (hslab u hu) hv)
    rw [hvB] at hh
    nlinarith only [hh,htail]
  have hs := Finset.sum_le_sum hp
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hi := separated_momentDecay_integral_le he
    (criticalExcess_nonneg v) (by norm_num : 2 ≤ 128) hU
  dsimp only [v] at hs hi
  nlinarith only [hs,hi]

end Montgomery.RationalMoment.RightDetector
