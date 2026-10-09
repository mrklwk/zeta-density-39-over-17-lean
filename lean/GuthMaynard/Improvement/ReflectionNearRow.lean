import GuthMaynard.Improvement.ReflectionNear
import GuthMaynard.Improvement.SourceDirichletPairing
import GuthMaynard.Improvement.AmplifierArithmetic
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Uniform source bound with the exact real-length index set. -/
theorem boundedPolynomial_norm_le_two_mul {N : ℝ} (hN : 2 ≤ N) (a : ℕ → ℂ)
    (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) (t : ℝ) :
    ‖boundedPolynomial N a t‖ ≤ 2*N := by
  have hh := (boundedPolynomial_regular N a).2 t
  have hc := amplifier_source_card (show 0 ≤ N by linarith)
  calc
    _ ≤ ∑ n ∈ sourceRatioIndices N, ‖a n‖ := hh
    _ ≤ ∑ _n ∈ sourceRatioIndices N, (1:ℝ) := Finset.sum_le_sum (fun n hn => ha n hn)
    _ = ((amplifierSource N).card:ℝ) := by simp [sourceRatioIndices,amplifierSource]
    _ ≤ N+1 := hc
    _ ≤ _ := by linarith

theorem source_density_pointwise_bound {N : ℝ} (hN : 2 ≤ N) (a : ℕ → ℂ)
    (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) (μ : ℝ → ℝ)
    (hμ : ∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) (t : ℝ) :
    μ t ≤ 4*N^2 := by
  have hh := boundedPolynomial_norm_le_two_mul hN a ha t
  nlinarith [hμ t,norm_nonneg (boundedPolynomial N a t)]

/-- Every ordinary interval has the same source-density mass bound, without a support premise. -/
theorem source_density_interval_mass {N : ℝ} (hN : 2 ≤ N) (a : ℕ → ℂ)
    (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) (μ : ℝ → ℝ)
    (hi : Integrable μ) (hμ : ∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2)
    {s t : ℝ} (hst : s ≤ t) :
    (∫ x in Icc s t, μ x) ≤ 4*N^2*(t-s) := by
  calc
    _ ≤ ∫ _x in Icc s t, (4*N^2) :=
      setIntegral_mono_on hi.integrableOn (integrableOn_const isCompact_Icc.measure_lt_top.ne)
        measurableSet_Icc (fun x _ => source_density_pointwise_bound hN a ha μ hμ x)
    _ = _ := by rw [setIntegral_const,Real.volume_real_Icc_of_le hst]; simp; ring

/-- Actual mass bound on a supported ordinary density, including zero time length. -/
theorem source_density_mass_bound {N T t₀ : ℝ} (hN : 2 ≤ N) (hT : 0 ≤ T)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) (μ : ℝ → ℝ)
    (hi : Integrable μ) (hs : Function.support μ ⊆ Icc t₀ (t₀+T))
    (hμ : ∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) :
    (∫ t, μ t) ≤ 4*N^2*T := by
  have hz : ∀ t, t ∉ Icc t₀ (t₀+T) → μ t=0 := by
    intro t ht
    exact Function.notMem_support.mp (fun hh => ht (hs hh))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ∫ _t in Icc t₀ (t₀+T), (4*N^2) :=
      setIntegral_mono_on hi.integrableOn (integrableOn_const isCompact_Icc.measure_lt_top.ne)
        measurableSet_Icc (fun t _ => source_density_pointwise_bound hN a ha μ hμ t)
    _ = _ := by rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith)]; simp; ring

/-- Actual global row integrability uses the checked uniform centered-kernel bound. -/
theorem centered_row_integrable (w : MathCollab.Density.ReflectionCutoff)
    {L : ℝ} (hL : 1 ≤ L) (u : ℝ) {μ : ℝ → ℝ} (hi : Integrable μ) :
    Integrable (fun t => μ t*‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2) := by
  have hs : ∀ x, x ∉ Icc (1/2:ℝ) 5 → (w x:ℂ)=0 := by
    intro x hx
    have hz : w x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (w.support hh))
    simp only [hz,Complex.ofReal_zero]
  obtain ⟨D,hD,hbound⟩ := centeredKernel_uniform_bound w.complex_smooth
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤5) hs
  have hm : Measurable (fun t => ‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2) :=
    ((centeredKernel_measurable w.complex_smooth.continuous.measurable _ _ _).comp
      (measurable_id.sub_const u)).norm.pow_const 2
  have hh := hi.bdd_mul (c := (D*L)^2) hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (by linarith))).mpr (hbound L (t-u) hL)))
  simpa only [mul_comm] using hh

/-- Near-region row estimate from the actual order-two centered-kernel error.
The cutoff-dependent constant precedes all lengths, densities and translates. -/
theorem centered_near_row_bound (w : MathCollab.Density.ReflectionCutoff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N L T t₀ u : ℝ, 2 ≤ N → N ≤ L → 0 ≤ T →
      ∀ (a : ℕ → ℂ) (μ : ℝ → ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) → Integrable μ → (∀ t, 0 ≤ μ t) →
      Function.support μ ⊆ Icc t₀ (t₀+T) →
      (∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) →
      (∫ t in {t : ℝ | |t-u| ≤ Real.pi*L/8},
        μ t*‖centeredKernel (fun x => (w x:ℂ)) (1/2) 5 L (t-u)‖^2) ≤ C*L*N*T := by
  obtain ⟨K,hK,hnear⟩ := centeredKernel_near w (A := 2) (by norm_num)
  refine ⟨4*K^2,by positivity,?_⟩
  intro N L T t₀ u hN hNL hT a μ ha hi h0 hs hμ
  have hL : 0 < L := by linarith
  have hrow := centered_row_integrable w (by linarith : 1 ≤ L) u hi
  have hmass := source_density_mass_bound hN hT a ha μ hi hs hμ
  have hS : MeasurableSet {t : ℝ | |t-u| ≤ Real.pi*L/8} := by measurability
  calc
    _ ≤ ∫ t in {t : ℝ | |t-u| ≤ Real.pi*L/8}, μ t*(K/L)^2 := by
      apply setIntegral_mono_on hrow.integrableOn (hi.mul_const _).integrableOn hS
      intro t ht
      apply mul_le_mul_of_nonneg_left _ (h0 t)
      have hh := hnear L (t-u) hL ht
      have he : K*L/L^2=K/L := by field_simp
      rw [he] at hh
      exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hK hL.le)).mpr hh
    _ = (K/L)^2*(∫ t in {t : ℝ | |t-u| ≤ Real.pi*L/8}, μ t) := by
      rw [integral_mul_const]; ring
    _ ≤ (K/L)^2*(4*N^2*T) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (setIntegral_le_integral hi (Filter.Eventually.of_forall h0)).trans hmass
    _ ≤ (4*K^2)*L*N*T := by
      have hNLsq : N^2 ≤ L^2 := by nlinarith
      have hLN : 1 ≤ L*N := by nlinarith
      have hdiv : N^2/L^2 ≤ 1 := (div_le_one (sq_pos_of_pos hL)).mpr hNLsq
      have he : (K/L)^2*(4*N^2*T) = (4*K^2*T)*(N^2/L^2) := by field_simp
      rw [he]
      calc
        _ ≤ 4*K^2*T := by simpa using mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 4*K^2*T)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hLN (show 0 ≤ 4*K^2*T by positivity)]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.boundedPolynomial_norm_le_two_mul
#print axioms GuthMaynard.Improvement.source_density_pointwise_bound
#print axioms GuthMaynard.Improvement.source_density_mass_bound
#print axioms GuthMaynard.Improvement.centered_row_integrable
#print axioms GuthMaynard.Improvement.centered_near_row_bound

#print axioms GuthMaynard.Improvement.source_density_interval_mass
