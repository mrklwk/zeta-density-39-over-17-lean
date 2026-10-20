module
public import GuthMaynard.Improvement.CenteredPoisson
public import GuthMaynard.Improvement.LogPoissonBudget

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff FourierTransform
namespace GuthMaynard.Improvement

def poissonModes (U : ℝ) : Finset ℤ := (Finset.Icc (-⌊U⌋) ⌊U⌋).erase 0

theorem mem_poissonModes (U : ℝ) (m : ℤ) :
    m ∈ poissonModes U ↔ m ≠ 0 ∧ |(m:ℝ)| ≤ U := by
  rw [poissonModes,Finset.mem_erase,Finset.mem_Icc,abs_le]
  constructor
  · rintro ⟨h0,ha,hb⟩
    have hn : -(m:ℝ) ≤ U := by
      have hz : -m ≤ ⌊U⌋ := by omega
      simpa using Int.le_floor.mp hz
    exact ⟨h0,by linarith,Int.le_floor.mp hb⟩
  · rintro ⟨h0,ha,hb⟩
    have hn : -m ≤ ⌊U⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact ⟨h0,by omega,Int.le_floor.mpr hb⟩

/-- Exact pointwise partition into the finite nonzero modes and the actual
Fourier remainder. In particular the zero mode never enters the tail. -/
theorem poisson_mode_partition (f : ℝ → ℂ) {L U : ℝ}
    (hL : 0 < L) (hU : 0 ≤ U) (m : ℤ) :
    (if m = 0 then 0 else 𝓕 f (L*(m:ℝ))) =
      (if m ∈ poissonModes U then 𝓕 f (L*(m:ℝ)) else 0) +
        poissonRemainder f L 0 (L*U) m := by
  have hh : L*U < |L*((m:ℝ)-0)| ↔ U < |(m:ℝ)| := by
    rw [sub_zero,abs_mul,abs_of_pos hL,mul_lt_mul_iff_right₀ hL]
  unfold poissonRemainder
  rw [if_congr hh rfl rfl]
  by_cases hm : m = 0
  · subst m
    simp [mem_poissonModes,not_lt.mpr hU]
  · by_cases hu : |(m:ℝ)| ≤ U
    · simp [mem_poissonModes,hm,hu,not_lt.mpr hu]
    · simp [mem_poissonModes,hm,hu,lt_of_not_ge hu]

/-- Exact finite truncation error for the literal centered kernel. -/
theorem centeredKernel_truncation {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u L U : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hL : 0 < L) (hU : 0 ≤ U)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (s : ℝ) :
    centeredKernel a l u L s -
      (L:ℂ)*(∑ m ∈ poissonModes U, 𝓕 (logModulated a s) (L*(m:ℝ))) =
      (L:ℂ)*∑' m : ℤ, poissonRemainder (logModulated a s) L 0 (L*U) m := by
  obtain ⟨C,hC,h⟩ := logModulated_poisson_tail ha hl hlu hs 0
  have ht := ((h s L 0 (L*U) hL (mul_nonneg hL.le hU)).1).of_norm
  have hf : Summable (fun m : ℤ => if m ∈ poissonModes U then 𝓕 (logModulated a s) (L*(m:ℝ)) else 0) := by
    apply summable_of_ne_finset_zero (s := poissonModes U)
    intro m hm
    simp [hm]
  rw [centeredKernel_poisson ha hl hlu hL hs s]
  simp_rw [poisson_mode_partition _ hL hU]
  rw [hf.tsum_add ht]
  have he : (∑' m : ℤ, if m ∈ poissonModes U then 𝓕 (logModulated a s) (L*(m:ℝ)) else 0) =
      ∑ m ∈ poissonModes U, 𝓕 (logModulated a s) (L*(m:ℝ)) := by
    rw [tsum_eq_sum (s := poissonModes U) (fun m hm => by simp [hm])]
    exact Finset.sum_congr rfl (fun m hm => by simp [hm])
  rw [he]
  ring

/-- Uniform approximation of the actual centered finite kernel by its
finite nonzero Fourier modes, with no Poisson identity premise. -/
theorem centeredKernel_truncation_negligible {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {η c : ℝ} (hη : 0 < η) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T L s : ℝ,
      1 ≤ T → 1 ≤ L → L ≤ T^2 → |s| ≤ c*T →
      ‖centeredKernel a l u L s -
        (L:ℂ)*(∑ m ∈ poissonModes (T^(1+η)/L), 𝓕 (logModulated a s) (L*(m:ℝ)))‖ ≤
        C*T^(-200:ℝ) := by
  obtain ⟨C,hC,h⟩ := log_poisson_negligible ha hl hlu hs hη hc
  refine ⟨C,hC,?_⟩
  intro T L s hT hL hLT hst
  have hLp : 0 < L := by linarith
  have hTp : 0 < T := by linarith
  rw [centeredKernel_truncation ha hl hlu hLp (by positivity) hs s]
  rw [mul_div_cancel₀ _ hLp.ne']
  exact (h T L s 0 hT hL hLT hst).2

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.mem_poissonModes
#print axioms GuthMaynard.Improvement.poisson_mode_partition
#print axioms GuthMaynard.Improvement.centeredKernel_truncation

#print axioms GuthMaynard.Improvement.centeredKernel_truncation_negligible
