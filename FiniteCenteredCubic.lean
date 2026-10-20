module
public import AtomicRetainedCubic
public import FiniteCubicPerturbation

@[expose] public section

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

theorem finite_cubic_uniform_bound (W : Finset ℝ) {K : ℝ → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ s, ‖K s‖ ≤ B) : ‖finiteCubic W K‖ ≤ B^3*(W.card:ℝ)^3 := by
  calc
    _ ≤ ∑ t ∈ W, ∑ u ∈ W, ∑ v ∈ W, ‖K (t-u)*K (u-v)*K (v-t)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun _ _ =>
        (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))))
    _ ≤ ∑ _t ∈ W, ∑ _u ∈ W, ∑ _v ∈ W, B^3 := by
      apply sum_le_sum
      intro t _
      apply sum_le_sum
      intro u _
      apply sum_le_sum
      intro v _
      simp only [norm_mul]
      calc
        _ ≤ B*B*B := by gcongr <;> exact hb _
        _ = _ := by ring
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

theorem card_le_card_sqrt (W : Finset ℝ) : (W.card:ℝ) ≤ (W.card:ℝ)*Real.sqrt (W.card:ℝ) := by
  by_cases hz : W.card=0
  · simp [hz]
  have hR : (1:ℝ) ≤ W.card := by exact_mod_cast (show 1 ≤ W.card by omega)
  have hs : 1 ≤ Real.sqrt (W.card:ℝ) := (Real.one_le_sqrt).mpr hR
  nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg W.card)]

/-- Full finite-set centered cubic, with fixed cutoff support [1/2,5].
The literal additive energy, diagonal and all near-diagonal triples are
included. Every Fourier, affine, cutoff and Poisson estimate is discharged. -/
theorem finite_centered_cubic_bound (w : MathCollab.Density.ReflectionCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T L t₀ : ℝ, 2 ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖finiteCubic W (MathCollab.Density.hKernel w L)‖ ≤
        C*T^ε*(T^2*(W.card:ℝ)*Real.sqrt (W.card:ℝ)+
          T*L*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ)) := by
  obtain ⟨η,C,T₀,hη,_hη1,hC,hT₀,hret⟩ := retained_atomic_cubic_estimate w hε
  obtain ⟨A,hA,happrox⟩ := centered_atomic_cubic_approximation w hη
  have hs : ∀ x, x ∉ Icc (1/2:ℝ) 5 → (w x:ℂ)=0 := by
    intro x hx
    have hz : w x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (w.support hh))
    simp [hz]
  obtain ⟨D,hD,huniform⟩ := centeredKernel_uniform_bound w.complex_smooth
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤5) hs
  let B := D^3*T₀^3*(T₀+1)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨5*C+4*A+B,by positivity,?_⟩
  intro T L t₀ hT hLl hLu W hW hsep
  let R : ℝ := W.card
  let E : ℝ := discreteAdditiveEnergy W
  let X := T^2*R*Real.sqrt R+T*L*Real.sqrt R*Real.sqrt E
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hL1 : 1 ≤ L := (Real.one_le_rpow hT1 (by norm_num : (0:ℝ)≤4/5)).trans hLl
  have hLp : 0 < L := by linarith
  have hLT2 : L ≤ T^2 := hLu.trans (by nlinarith)
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hE : 0 ≤ E := Nat.cast_nonneg _
  have hRcard : R ≤ T+1 := separated_interval_card hTp.le W hW hsep
  have hR2 : R^2 ≤ 4*T^2 := by
    have hh := pow_le_pow_left₀ hR (show R ≤ 2*T by linarith) 2
    nlinarith
  have hsqrt : R ≤ R*Real.sqrt R := card_le_card_sqrt W
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hbase : T^2*R*Real.sqrt R ≤ X := by
    exact le_add_of_nonneg_right (by positivity)
  have hTe : 1 ≤ T^ε := Real.one_le_rpow hT1 hε.le
  have hpowX : X ≤ T^ε*X := by nlinarith
  have hR3 : R^3 ≤ 4*X := by
    have hh := mul_le_mul_of_nonneg_right hR2 hR
    have hh' := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 4*T^2 by positivity)
    nlinarith
  have hErr (q : ℝ) (hq : q ≤ 0) : T^q*R^3 ≤ 4*T^ε*X := by
    have hp : T^q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 hq
    have hh := mul_le_mul_of_nonneg_right hp (pow_nonneg hR 3)
    nlinarith
  by_cases hbig : T₀ ≤ T
  · let J := kernelCubic (finiteTimeMeasure W)
      (retainedPoissonKernel (volume.restrict (Icc (1/2:ℝ) 5)) (fun x => (w x:ℂ)) L
        (poissonModes (T^(1+η)/L)))
    have hj : ‖J‖ ≤ C*(T^ε*X+T^(-100:ℝ)*R^3) := hret T L hbig hLl hLu W hsep
    have hd : ‖finiteCubic W (MathCollab.Density.hKernel w L)-J‖ ≤ A*T^(-190:ℝ)*R^3 :=
      happrox T L t₀ hT1 hL1 hLT2 W hW
    calc
      _ = ‖J+(finiteCubic W (MathCollab.Density.hKernel w L)-J)‖ := by congr 1; ring
      _ ≤ ‖J‖+‖finiteCubic W (MathCollab.Density.hKernel w L)-J‖ := norm_add_le _ _
      _ ≤ C*(T^ε*X+T^(-100:ℝ)*R^3)+A*T^(-190:ℝ)*R^3 := add_le_add hj hd
      _ ≤ C*(T^ε*X+4*T^ε*X)+A*(4*T^ε*X) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hErr (-100) (by norm_num))) hC.le)
          (by convert mul_le_mul_of_nonneg_left (hErr (-190) (by norm_num)) hA using 1; ring)
      _ ≤ (5*C+4*A+B)*T^ε*X := by nlinarith only [mul_nonneg hB (show 0 ≤ T^ε*X by positivity)]
  · have hTT : T ≤ T₀ := le_of_not_ge hbig
    have hRR : R ≤ T₀+1 := hRcard.trans (by linarith)
    have hRsmall : R^3 ≤ (T₀+1)^2*(R*Real.sqrt R) := by
      have hp := pow_le_pow_left₀ hR hRR 2
      have hh := mul_le_mul_of_nonneg_right hp hR
      have hh' := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg (T₀+1))
      nlinarith
    have hnorm : ∀ s, ‖MathCollab.Density.hKernel w L s‖ ≤ D*L := by
      intro s
      rw [← centeredKernel_eq_density_hKernel w hLp]
      exact huniform L s hL1
    have hh := finite_cubic_uniform_bound W (show 0 ≤ D*L by positivity) hnorm
    have hrootbase : R*Real.sqrt R ≤ X := by
      have hh := mul_le_mul_of_nonneg_right (show 1 ≤ T^2 by nlinarith) (show 0 ≤ R*Real.sqrt R by positivity)
      nlinarith
    calc
      _ ≤ (D*L)^3*R^3 := hh
      _ ≤ (D*T₀)^3*((T₀+1)^2*(R*Real.sqrt R))  := by
        gcongr
        exact hLu.trans hTT
      _ = B*(R*Real.sqrt R) := by dsimp [B]; ring
      _ ≤ B*(T^ε*X) := mul_le_mul_of_nonneg_left (hrootbase.trans hpowX) hB
      _ ≤ (5*C+4*A+B)*T^ε*X := by
        nlinarith only [mul_nonneg (show 0 ≤ 5*C+4*A by positivity) (show 0 ≤ T^ε*X by positivity)]

/-- The literal squared-cutoff finite matrix satisfies the cubic estimate
needed by the signed amplifier. The cutoff is the same one, without a
change of support or plateau and without a thinning hypothesis. -/
theorem centered_matrix_cubic_bound (w : MathCollab.Density.ReflectionCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T L t₀ : ℝ, 2 ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖Matrix.trace (cutoffCenteredMatrix w L W^3)‖ ≤
        C*T^ε*(T^2*(W.card:ℝ)*Real.sqrt (W.card:ℝ)+
          T*L*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ)) := by
  obtain ⟨C,hC,h⟩ := finite_centered_cubic_bound (reflectionSquare w) hε
  refine ⟨C,hC,?_⟩
  intro T L t₀ hT hLl hLu W hW hsep
  rw [finite_cubic_trace]
  exact h T L t₀ hT hLl hLu W hW hsep

end Montgomery.RationalMoment
