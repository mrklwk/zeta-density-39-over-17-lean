module
public import LaterPairs.PhysicalLongMultiplicity
public import ActualLongTailReduction
public import TwoPowerTailTransfer
public import MathCollab.Density.Stronger.LongScalarBudget

@[expose] public section

open Real Complex Filter MeasureTheory Set
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density

theorem criticalMeanThreshold_eventually {C σ a δ : ℝ}
    (hC : 0 < C) (hw : PhysicalDetectorWindow σ a) 
    (hδ : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ criticalMeanThreshold C σ a δ T ∧
        48*Real.pi*T^(-125:ℝ) ≤ criticalMeanThreshold C σ a δ T := by
  have hc := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/96)).eventually
    (eventually_ge_atTop (48*C))
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (48*Real.pi),hc,
    log_pow_eventually_le_rpow 1 (by norm_num : (0:ℝ)<1/96)] with T hT hπ hconst hlog
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlogp : 0 < Real.log T := Real.log_pos (by linarith)
  have hXp : 0 < detectorX δ T := Real.rpow_pos_of_pos hTp _
  have hsqrt : Real.sqrt (detectorX δ T)=T^(δ/2) := by
    rw [Real.sqrt_eq_rpow,detectorX,← Real.rpow_mul hTp.le]
    congr 1
    ring
  have hYpow : (detectorY a T)^((σ-1/2)/2)=T^((3*a/4)*(σ-1/2)) := by
    rw [detectorY,smoothingExponent,← Real.rpow_mul hTp.le]
    congr 1
    ring
  have hexp : δ/2+1/48 ≤ (3*a/4)*(σ-1/2) := by
    linarith [hw.threshold]
  have hden : 48*C*Real.sqrt (detectorX δ T)*Real.log T ≤
      (detectorY a T)^((σ-1/2)/2) := by
    calc
      _ ≤ T^(1/96:ℝ)*T^(δ/2)*T^(1/96:ℝ) := by rw [hsqrt]; gcongr; simpa only [pow_one] using hlog
      _ = T^(δ/2+1/48) := by
        rw [← Real.rpow_add hTp,← Real.rpow_add hTp]
        congr 1
        ring
      _ ≤ _ := by rw [hYpow]; exact Real.rpow_le_rpow_of_exponent_le hT1 hexp
  have hb : 1 ≤ criticalMeanThreshold C σ a δ T := by
    unfold criticalMeanThreshold
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hden)
  refine ⟨hb,le_trans ?_ hb⟩
  have hp : T ≤ T^125 := by simpa only [pow_one] using
    (pow_le_pow_right₀ hT1 (by norm_num : 1 ≤ 125))
  rw [Real.rpow_neg hTp.le,show (125:ℝ)=((125:ℕ):ℝ) by norm_num,Real.rpow_natCast,
    ← div_eq_mul_inv]
  exact (div_le_one (by positivity)).mpr (hπ.trans hp)

/-- Every complementary actual zero, with its analytic multiplicity, is
counted by the literal critical-zeta excess integral. No zeta-tail or
moment bound is a premise; this isolates the missing physical tail producer. -/
theorem smoothLongZeroCount_excess_reduction {σ a δ η : ℝ}
    (hw : PhysicalDetectorWindow σ a) 
    (hδ : 0 < δ) (hδcap : δ ≤ 1/8) (hη : 0 < η) :
    ∃ C D : ℝ,0 < C ∧ 0 < D ∧ ∀ᶠ T : ℝ in atTop,
      (smoothLongZeroCount η σ a δ T:ℝ)*criticalMeanThreshold C σ a δ T ≤
        D*Real.log T*(∫ t in Icc 0 (3*T),
          criticalExcess (criticalMeanThreshold C σ a δ T/(4*Real.pi)) t) := by
  classical
  obtain ⟨Cm,hCm,hmean⟩ := smoothLongZeroFinset_eventually_detects_mean hw hδ hδcap hη
  obtain ⟨Cb,hCb,hlocal⟩ := zeta_local_multiplicity_bound
  let D : ℝ := 8*Cb*(separationMass+1)
  have hD : 0 < D := by dsimp [D]; positivity [separationMass_nonneg]
  refine ⟨Cm,D,hCm,hD,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),hmean,
    criticalMeanThreshold_eventually hCm hw hδcap] with T hT hm hb
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog2 : 0 ≤ Real.log (2*T) := Real.log_nonneg (by linarith)
  have hlogs : Real.log (2*T) ≤ 2*Real.log T := by
    rw [Real.log_mul (by norm_num) hTp.ne']
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hT
    linarith
  have hbin (k : ℤ) : (∑ ρ ∈ (smoothLongZeroFinset η σ a δ T).filter (fun ρ => ordinateBin ρ=k),
      (zetaMultiplicity ρ:ℝ)) ≤ Cb*Real.log (2*T) := by
    have hs : (smoothLongZeroFinset η σ a δ T).filter (fun ρ => ordinateBin ρ=k) ⊆
        (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ=k) := by
      intro ρ hρ
      exact Finset.mem_filter.mpr
        ⟨smoothLongZeroFinset_subset η σ a δ T (Finset.mem_filter.mp hρ).1,(Finset.mem_filter.mp hρ).2⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
      (hlocal σ T hw.sigma_low.le hT k)
  obtain ⟨R,hR,hcard,hsep,hcount⟩ := weighted_separated_extraction
    (smoothLongZeroFinset η σ a δ T) (fun ρ => (zetaMultiplicity ρ:ℝ))
    (by positivity : 0 ≤ Cb*Real.log (2*T)) hbin
  let U := R.image Complex.im
  have hUslab : ∀ u ∈ U,u ∈ Icc T (2*T) := by
    intro u hu
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hu
    have hz := mem_zetaZeroFinset.mp (smoothLongZeroFinset_subset η σ a δ T (hR hρ))
    exact ⟨hz.2.2.1,hz.2.2.2⟩
  have hUm : ∀ u ∈ U,criticalMeanThreshold Cm σ a δ T ≤ weightedCriticalMean 128 u := by
    intro u hu
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hu
    unfold criticalMeanThreshold
    apply (div_le_iff₀ (by have := Real.log_pos (by linarith : 1<T); unfold detectorX; positivity)).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hm ρ (hR hρ)
  have hcount' : (smoothLongZeroCount η σ a δ T:ℝ) ≤ 4*Cb*Real.log T*(U.card:ℝ) := by
    rw [← hcard] at hcount
    have hh : (smoothLongZeroCount η σ a δ T:ℝ) ≤ 2*(Cb*Real.log (2*T))*(U.card:ℝ) := by
      simpa only [smoothLongZeroCount,Nat.cast_sum] using hcount
    apply hh.trans
    have hs := mul_le_mul_of_nonneg_right hlogs (show 0 ≤ 2*Cb*(U.card:ℝ) by positivity)
    nlinarith only [hs]
  have hB : 0 < criticalMeanThreshold Cm σ a δ T := by linarith [hb.1]
  have hh := separated_weightedCriticalMean_excess_count hT1 hB hb.2 U hsep hUslab hUm
  let I : ℝ := ∫ t in Icc 0 (3*T),criticalExcess (criticalMeanThreshold Cm σ a δ T/(4*Real.pi)) t
  have hI : 0 ≤ I := integral_nonneg (criticalExcess_nonneg _)
  calc
    _ ≤ (4*Cb*Real.log T*(U.card:ℝ))*criticalMeanThreshold Cm σ a δ T :=
      mul_le_mul_of_nonneg_right hcount' hB.le
    _ = (4*Cb*Real.log T)*((U.card:ℝ)*criticalMeanThreshold Cm σ a δ T) := by ring
    _ ≤ (4*Cb*Real.log T)*(2*separationMass*I) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ _ := by
      change (4*Cb*Real.log T)*(2*separationMass*I) ≤ D*Real.log T*I
      dsimp [D]
      nlinarith [mul_nonneg (show 0 ≤ 8*Cb*Real.log T by positivity) hI]

end Montgomery.RationalMoment.RightDetector.Physical
