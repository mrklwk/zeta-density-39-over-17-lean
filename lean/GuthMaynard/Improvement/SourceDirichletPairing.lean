module
public import GuthMaynard.Improvement.SourceRatioAssembly
public import GuthMaynard.Improvement.Target
public import GuthMaynard.Improvement.OperatorPhase
public import GuthMaynard.Improvement.CenteredKernelBridge

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ComplexConjugate
namespace GuthMaynard.Improvement

def sourcePhasePolynomial {ι : Type*} (S : Finset ι) (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n*phase (ξ n*t)

/-- Literal finite polynomial pairing with the actual ordinary Fourier transform. -/
theorem source_phase_polynomial_pairing {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ t, (‖sourcePhasePolynomial S a ξ t‖^2:ℂ)*f t) =
      ∑ n ∈ S, ∑ m ∈ S, a n*conj (a m)*𝓕 f (ξ m-ξ n) := by
  have he (t : ℝ) : (‖sourcePhasePolynomial S a ξ t‖^2:ℂ)*f t =
      ∑ n ∈ S, ∑ m ∈ S, (a n*conj (a m))*(phase (-(ξ m-ξ n)*t)*f t) := by
    rw [← Complex.mul_conj']
    simp only [sourcePhasePolynomial,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    rw [operator_phase_conj]
    calc
      _ = (a n*conj (a m))*((phase (ξ n*t)*phase (-(ξ m*t)))*f t) := by ring
      _ = _ := by rw [← phase_add]; congr 3; ring
  have ht (n m : ι) : Integrable (fun t => (a n*conj (a m))*(phase (-(ξ m-ξ n)*t)*f t)) :=
    (integrable_phase_mul hf (ξ m-ξ n)).const_mul _
  simp_rw [he]
  rw [integral_finsetSum S (fun n _ => integrable_finsetSum _ (fun m _ => ht n m))]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_finsetSum S (fun m _ => ht n m)]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_const_mul,fourier_eq_phase_integral]

/-- Bounded coefficients give exactly the unweighted ratio-sampling consumer. -/
theorem source_phase_polynomial_pairing_bound {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (ξ : ι → ℝ) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    {f : ℝ → ℂ} (hf : Integrable f) :
    ‖∫ t, (‖sourcePhasePolynomial S a ξ t‖^2:ℂ)*f t‖ ≤
      ∑ n ∈ S, ∑ m ∈ S, ‖𝓕 f (ξ m-ξ n)‖ := by
  rw [source_phase_polynomial_pairing S a ξ hf]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  rw [norm_mul,norm_mul,RCLike.norm_conj]
  have hh : ‖a n‖*‖a m‖ ≤ 1 := by nlinarith [ha n hn,ha m hm,norm_nonneg (a n),norm_nonneg (a m)]
  simpa using mul_le_mul_of_nonneg_right hh (norm_nonneg _)

theorem boundedPolynomial_phase (N : ℝ) (a : ℕ → ℂ) (t : ℝ) :
    boundedPolynomial N a t = sourcePhasePolynomial (Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊) a
      (fun n => mellinFrequency ((n:ℝ)/N)) t := by
  unfold boundedPolynomial sourcePhasePolynomial
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_comm (mellinFrequency _) t,mellinFrequency_phase]

/-- The literal target polynomial is measurable and bounded independently of time. -/
theorem boundedPolynomial_regular (N : ℝ) (a : ℕ → ℂ) :
    Continuous (boundedPolynomial N a) ∧
    ∀ t, ‖boundedPolynomial N a t‖ ≤ ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, ‖a n‖ := by
  constructor
  · unfold boundedPolynomial
    fun_prop
  · intro t
    rw [boundedPolynomial_phase]
    unfold sourcePhasePolynomial
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => by rw [norm_mul,phase_norm,mul_one])


/-- The literal bounded-coefficient target polynomial is controlled by the
actual normalized logarithmic ratio samples, for every real positive N. -/
theorem boundedPolynomial_pairing_ratio_bound {N : ℝ} (hN : 0 < N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1)
    {f : ℝ → ℂ} (hf : Integrable f) :
    ‖∫ t, (‖boundedPolynomial N a t‖^2:ℂ)*f t‖ ≤
      ∑ n ∈ sourceRatioIndices N, ∑ m ∈ sourceRatioIndices N,
        ‖𝓕 f (Real.log ((n:ℝ)/m)/(2*Real.pi))‖ := by
  have hp (n : ℕ) (hn : n ∈ sourceRatioIndices N) : 0 < (n:ℝ) :=
    hN.trans ((sourceRatioIndices_mem hN.le n).mp hn).1
  have he (n m : ℕ) (hn : n ∈ sourceRatioIndices N) (hm : m ∈ sourceRatioIndices N) :
      mellinFrequency ((n:ℝ)/N)-mellinFrequency ((m:ℝ)/N) = Real.log ((n:ℝ)/m)/(2*Real.pi) := by
    unfold mellinFrequency
    rw [Real.log_div (hp n hn).ne' hN.ne',Real.log_div (hp m hm).ne' hN.ne',
      Real.log_div (hp n hn).ne' (hp m hm).ne']
    ring
  have hh := source_phase_polynomial_pairing_bound (sourceRatioIndices N) a
    (fun n => mellinFrequency ((n:ℝ)/N)) ha hf
  have hid : boundedPolynomial N a = sourcePhasePolynomial (sourceRatioIndices N) a
      (fun n => mellinFrequency ((n:ℝ)/N)) := funext (boundedPolynomial_phase N a)
  rw [← hid] at hh
  refine hh.trans_eq ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [he n m hn hm]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.source_phase_polynomial_pairing
#print axioms GuthMaynard.Improvement.source_phase_polynomial_pairing_bound
#print axioms GuthMaynard.Improvement.boundedPolynomial_phase
#print axioms GuthMaynard.Improvement.boundedPolynomial_regular

#print axioms GuthMaynard.Improvement.boundedPolynomial_pairing_ratio_bound
