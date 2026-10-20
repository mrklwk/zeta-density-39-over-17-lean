module
public import FiniteCubicBasics
public import GuthMaynard.Improvement.RetainedRadialAssembly

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- Equality on the actual difference window preserves every triple,
including repeated indices and closed endpoints. -/
theorem finite_cubic_congr_window (W : Finset ℝ) {T : ℝ} {K J : ℝ → ℂ}
    (hW : ∀ t ∈ W, ∀ u ∈ W, |t-u| ≤ T) (he : ∀ s, |s| ≤ T → K s=J s) :
    finiteCubic W K=finiteCubic W J := by
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  rw [he _ (hW t ht u hu),he _ (hW u hu v hv),he _ (hW v hv t ht)]

/-- Local Poisson perturbation with the literal atomic mass cubed.
No L2 approximation density enters the error term. -/
theorem finite_cubic_local_perturbation (W : Finset ℝ) {T B e : ℝ}
    {K J : ℝ → ℂ} (hK : Measurable K) (hJ : Measurable J) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hW : ∀ t ∈ W, ∀ u ∈ W, |t-u| ≤ T)
    (hbK : ∀ s, |s| ≤ T → ‖K s‖ ≤ B) (hbJ : ∀ s, |s| ≤ T → ‖J s‖ ≤ B)
    (herr : ∀ s, |s| ≤ T → ‖K s-J s‖ ≤ e) :
    ‖finiteCubic W K-finiteCubic W J‖ ≤ 3*e*B^2*(W.card:ℝ)^3 := by
  let A := {s : ℝ | |s| ≤ T}
  have hA : MeasurableSet A := measurableSet_le measurable_id.abs measurable_const
  have hk (s : ℝ) : ‖A.indicator K s‖ ≤ B := by
    by_cases hs : s ∈ A
    · simpa only [indicator_of_mem hs] using hbK s hs
    · simp only [indicator_of_notMem hs,norm_zero]; exact hB
  have hj (s : ℝ) : ‖A.indicator J s‖ ≤ B := by
    by_cases hs : s ∈ A
    · simpa only [indicator_of_mem hs] using hbJ s hs
    · simp only [indicator_of_notMem hs,norm_zero]; exact hB
  have hd (s : ℝ) : ‖A.indicator K s-A.indicator J s‖ ≤ e := by
    by_cases hs : s ∈ A
    · simpa only [indicator_of_mem hs] using herr s hs
    · simp only [indicator_of_notMem hs,sub_self,norm_zero]; exact he
  rw [finite_cubic_congr_window W hW (J := A.indicator K) (fun s hs => (indicator_of_mem (show s ∈ A from hs) K).symm),
    finite_cubic_congr_window W hW (J := A.indicator J) (fun s hs => (indicator_of_mem (show s ∈ A from hs) J).symm)]
  rw [← finite_cubic_integral W (hK.indicator hA) hB hk,
    ← finite_cubic_integral W (hJ.indicator hA) hB hj]
  simpa only [finite_time_mass] using kernelCubic_perturbation (finiteTimeMeasure W)
    (hK.indicator hA) (hJ.indicator hA) hB he hk hj hd

/-- Each retained frequency kernel is globally bounded, with the actual
finite mode set; this assertion carries no asymptotic estimate premise. -/
theorem retained_poisson_kernel_bounded (w : MathCollab.Density.ReflectionCutoff)
    (L : ℝ) (S : Finset ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, ‖retainedPoissonKernel (volume.restrict (Icc (1/2:ℝ) 5))
      (fun x => (w x:ℂ)) L S s‖ ≤ B := by
  have hs : ∀ x, x ∉ Icc (1/2:ℝ) 5 → (w x:ℂ)=0 := by
    intro x hx
    have hz : w x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (w.support hh))
    simp [hz]
  obtain ⟨B,hB,hb⟩ := assembly_cutoff_bound w.complex_smooth.continuous hs
  refine ⟨(volume.restrict (Icc (1/2:ℝ) 5)).real univ*(|L| *S.card*B),by positivity,?_⟩
  intro s
  change ‖∫ x, retainedAmplitude (fun x => (w x:ℂ)) L S x*GuthMaynard.Improvement.phase (s*mellinFrequency x)
    ∂volume.restrict (Icc (1/2:ℝ) 5)‖ ≤ _
  rw [mul_comm ((volume.restrict (Icc (1/2:ℝ) 5)).real univ)]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with x
  rw [norm_mul,phase_norm,mul_one]
  exact retainedAmplitude_bound hB.le hb L S x

/-- Full atomic Poisson approximation, retaining every diagonal and near
triple. Its error is uniform and has no inverse smoothing-width factor. -/
theorem centered_atomic_cubic_approximation (w : MathCollab.Density.ReflectionCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T L t₀ : ℝ, 1 ≤ T → 1 ≤ L → L ≤ T^2 →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Icc t₀ (t₀+T)) →
      ‖finiteCubic W (MathCollab.Density.hKernel w L)-
        kernelCubic (finiteTimeMeasure W) (retainedPoissonKernel (volume.restrict (Icc (1/2:ℝ) 5))
          (fun x => (w x:ℂ)) L (poissonModes (T^(1+η)/L)))‖ ≤
      C*T^(-190:ℝ)*(W.card:ℝ)^3 := by
  have hs : ∀ x, x ∉ Icc (1/2:ℝ) 5 → (w x:ℂ)=0 := by
    intro x hx
    have hz : w x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (w.support hh))
    simp [hz]
  obtain ⟨E,hE,herr⟩ := centeredKernel_truncation_negligible w.complex_smooth
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤5) hs hη (show (0:ℝ)≤1 by norm_num)
  obtain ⟨D,hD,hbound⟩ := centeredKernel_uniform_bound w.complex_smooth
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤5) hs
  obtain ⟨B,hB,hb⟩ := assembly_cutoff_bound w.complex_smooth.continuous hs
  refine ⟨3*E*(D+E)^2,by positivity,?_⟩
  intro T L t₀ hT hL hLT W hW
  let J := retainedPoissonKernel (volume.restrict (Icc (1/2:ℝ) 5))
    (fun x => (w x:ℂ)) L (poissonModes (T^(1+η)/L))
  let K := centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := by linarith
  have he (s : ℝ) (hst : |s| ≤ T) : ‖K s-J s‖ ≤ E*T^(-200:ℝ) := by
    dsimp only [J,K]
    rw [retainedPoissonKernel_fourier w.complex_smooth.continuous.measurable hb hs]
    exact herr T L s hT hL hLT (by simpa only [one_mul] using hst)
  have hd (s : ℝ) (_hst : |s| ≤ T) : ‖K s‖ ≤ (D+E)*L :=
    (hbound L s hL).trans (by nlinarith)
  have hj (s : ℝ) (hst : |s| ≤ T) : ‖J s‖ ≤ (D+E)*L := by
    have hp : T^(-200:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num)
    calc
      _ = ‖K s-(K s-J s)‖ := by congr 1; ring
      _ ≤ ‖K s‖+‖K s-J s‖ := norm_sub_le _ _
      _ ≤ D*L+E*T^(-200:ℝ) := add_le_add (hbound L s hL) (he s hst)
      _ ≤ _ := by nlinarith
  have hdist (t : ℝ) (ht : t ∈ W) (u : ℝ) (hu : u ∈ W) : |t-u| ≤ T := by
    obtain ⟨ht₁,ht₂⟩ := hW t ht
    obtain ⟨hu₁,hu₂⟩ := hW u hu
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hJm : Measurable J := retainedPoissonKernel_measurable _ w.complex_smooth.continuous.measurable L _
  have hp := finite_cubic_local_perturbation W
    (centeredKernel_measurable w.complex_smooth.continuous.measurable _ _ _) hJm
    (show 0 ≤ (D+E)*L by positivity) (show 0 ≤ E*T^(-200:ℝ) by positivity)
    hdist hd hj he
  obtain ⟨B',hB',hb'⟩ := retained_poisson_kernel_bounded w L (poissonModes (T^(1+η)/L))
  rw [← finite_cubic_integral W hJm hB' hb'] at hp
  have heK : K = MathCollab.Density.hKernel w L := by
    funext s
    exact centeredKernel_eq_density_hKernel w hLp s
  dsimp only [K] at heK
  rw [heK] at hp
  have hscale : T^(-200:ℝ)*L^2 ≤ T^(-190:ℝ) := by
    calc
      _ ≤ T^(-200:ℝ)*(T^2)^2 := by gcongr
      _ = T^(-196:ℝ) := by
        rw [show (T^2)^2=T^4 by ring,← Real.rpow_natCast T 4,← Real.rpow_add hTp]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  calc
    _ ≤ 3*(E*T^(-200:ℝ))*((D+E)*L)^2*(W.card:ℝ)^3 := hp
    _ = (3*E*(D+E)^2)*(T^(-200:ℝ)*L^2)*(W.card:ℝ)^3 := by ring
    _ ≤ _ := by gcongr

end Montgomery.RationalMoment
