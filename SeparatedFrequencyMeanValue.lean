module
public import GuthMaynard.Improvement.DirichletMeanValue
public import GuthMaynard.Improvement.SamplingVariation
public import RationalDifferenceEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Set
open scoped ComplexConjugate
namespace Montgomery.RationalMoment

variable {ι : Type*}

/-- One side of a separated frequency row has only a harmonic reciprocal loss. -/
theorem reciprocal_separated_sum (S : Finset ι) (f : ι → ℝ)
    {δ L : ℝ} (hδ : 0 < δ)
    (hf : ∀ i ∈ S, δ ≤ f i ∧ f i ≤ L)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |f i - f j|) :
    (∑ i ∈ S, (f i)⁻¹) ≤ δ⁻¹ * (1 + Real.log ⌊L / δ⌋₊) := by
  classical
  let g : ι → ℕ := fun i => ⌊f i / δ⌋₊
  let N : ℕ := ⌊L / δ⌋₊
  have hg (i : ι) (hi : i ∈ S) : 1 ≤ g i ∧ g i ≤ N := by
    refine ⟨Nat.le_floor ((le_div_iff₀ hδ).mpr (by simpa using (hf i hi).1)), ?_⟩
    exact Nat.floor_mono (div_le_div_of_nonneg_right (hf i hi).2 hδ.le)
  have hinj : Set.InjOn g S := by
    intro i hi j hj he
    by_contra hne
    have hfi : 0 ≤ f i / δ := div_nonneg (hδ.le.trans (hf i hi).1) hδ.le
    have hfj : 0 ≤ f j / δ := div_nonneg (hδ.le.trans (hf j hj).1) hδ.le
    have hli : (g i : ℝ) ≤ f i / δ := Nat.floor_le hfi
    have hlj : (g j : ℝ) ≤ f j / δ := Nat.floor_le hfj
    have hui : f i / δ < (g i : ℝ) + 1 := Nat.lt_floor_add_one _
    have huj : f j / δ < (g j : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [he] at hli hui
    have hab : |f i / δ - f j / δ| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    rw [← sub_div, abs_div, abs_of_pos hδ] at hab
    have hh := (div_lt_iff₀ hδ).mp hab
    linarith [hsep i hi j hj hne]
  have hsub : S.image g ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    exact mem_Icc.mpr (hg i hi)
  calc
    _ ≤ ∑ i ∈ S, δ⁻¹ * (g i : ℝ)⁻¹ := by
      apply sum_le_sum
      intro i hi
      have hgpos : (0 : ℝ) < g i := by exact_mod_cast (hg i hi).1
      have hfloor : (g i : ℝ) * δ ≤ f i :=
        (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg (hδ.le.trans (hf i hi).1) hδ.le))
      have hh := inv_anti₀ (mul_pos hgpos hδ) hfloor
      simpa [mul_inv_rev] using hh
    _ = δ⁻¹ * ∑ n ∈ S.image g, (n : ℝ)⁻¹ := by rw [sum_image hinj, mul_sum]
    _ ≤ δ⁻¹ * ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log N) (by positivity)

theorem reciprocal_frequency_row [DecidableEq ι] (S : Finset ι) (ω : ι → ℝ)
    {δ L : ℝ} (hδ : 0 < δ) (hω : ∀ i ∈ S, |ω i| ≤ L)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |ω i - ω j|)
    {n : ι} (hn : n ∈ S) :
    (∑ m ∈ S.erase n, |ω n - ω m|⁻¹) ≤
      2 * δ⁻¹ * (1 + Real.log ⌊2 * L / δ⌋₊) := by
  classical
  let A := (S.erase n).filter (fun m => ω m < ω n)
  let B := (S.erase n).filter (fun m => ¬ω m < ω n)
  have habs (m : ι) (hm : m ∈ S) : |ω n - ω m| ≤ 2 * L :=
    (abs_sub _ _).trans (by linarith [hω n hn, hω m hm])
  have hleft := reciprocal_separated_sum A (fun m => ω n - ω m) hδ
    (fun m hm => by
      obtain ⟨hm, hlt⟩ := mem_filter.mp hm
      have he := (mem_erase.mp hm).1
      have hs := hsep n hn m (mem_of_mem_erase hm) he.symm
      rw [abs_of_pos (sub_pos.mpr hlt)] at hs
      exact ⟨hs, (le_abs_self _).trans (habs m (mem_of_mem_erase hm))⟩)
    (fun i hi j hj hne => by
      have hh := hsep i (mem_of_mem_erase (mem_filter.mp hi).1)
        j (mem_of_mem_erase (mem_filter.mp hj).1) hne
      simpa [show ω n - ω i - (ω n - ω j) = -(ω i - ω j) by ring, abs_sub_comm] using hh)
  have hright := reciprocal_separated_sum B (fun m => ω m - ω n) hδ
    (fun m hm => by
      obtain ⟨hm, hlt⟩ := mem_filter.mp hm
      have he := (mem_erase.mp hm).1
      have hs := hsep m (mem_of_mem_erase hm) n hn he
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hlt))] at hs
      exact ⟨hs, (le_abs_self _).trans (by simpa [abs_sub_comm] using habs m (mem_of_mem_erase hm))⟩)
    (fun i hi j hj hne => by
      have hh := hsep i (mem_of_mem_erase (mem_filter.mp hi).1)
        j (mem_of_mem_erase (mem_filter.mp hj).1) hne
      simpa only [sub_sub_sub_cancel_right] using hh)
  have hl : (∑ m ∈ A, |ω n - ω m|⁻¹) = ∑ m ∈ A, (ω n - ω m)⁻¹ := by
    apply sum_congr rfl
    intro m hm
    rw [abs_of_pos (sub_pos.mpr (mem_filter.mp hm).2)]
  have hr : (∑ m ∈ B, |ω n - ω m|⁻¹) = ∑ m ∈ B, (ω m - ω n)⁻¹ := by
    apply sum_congr rfl
    intro m hm
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt (mem_filter.mp hm).2))]
  have he := sum_filter_add_sum_filter_not (S.erase n) (fun m => ω m < ω n)
    (fun m => |ω n - ω m|⁻¹)
  change (∑ m ∈ A, |ω n - ω m|⁻¹) + (∑ m ∈ B, |ω n - ω m|⁻¹) = _ at he
  rw [← he, hl, hr]
  linarith

def exponentialPhase (ω t : ℝ) : ℂ := Complex.exp (Complex.I * (ω : ℂ) * t)
def exponentialPolynomial (S : Finset ι) (ω : ι → ℝ) (c : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, c n * exponentialPhase (ω n) t

theorem exponentialPhase_norm (ω t : ℝ) : ‖exponentialPhase ω t‖ = 1 := by
  simp [exponentialPhase, Complex.norm_exp]

theorem exponentialPolynomial_continuous (S : Finset ι) (ω : ι → ℝ) (c : ι → ℂ) :
    Continuous (exponentialPolynomial S ω c) := by
  unfold exponentialPolynomial exponentialPhase
  fun_prop

theorem exponentialPhase_pair (ω ν t : ℝ) :
    exponentialPhase ω t * conj (exponentialPhase ν t) = exponentialPhase (ω - ν) t := by
  unfold exponentialPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

theorem exponential_gram (S : Finset ι) (ω : ι → ℝ) (c : ι → ℂ) (a b : ℝ) :
    (∫ t in Set.Icc a b, (‖exponentialPolynomial S ω c t‖ ^ 2 : ℂ)) =
      ∑ n ∈ S, ∑ m ∈ S, (c n * conj (c m)) *
        (∫ t in Set.Icc a b, exponentialPhase (ω n) t * conj (exponentialPhase (ω m) t)) := by
  have he (t : ℝ) : (‖exponentialPolynomial S ω c t‖ ^ 2 : ℂ) =
      ∑ n ∈ S, ∑ m ∈ S, (c n * conj (c m)) *
        (exponentialPhase (ω n) t * conj (exponentialPhase (ω m) t)) := by
    rw [← Complex.mul_conj']
    simp only [exponentialPolynomial, map_sum, map_mul, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro m _
    ring
  have ht (n m : ι) : IntegrableOn
      (fun t => (c n * conj (c m)) *
        (exponentialPhase (ω n) t * conj (exponentialPhase (ω m) t))) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    unfold exponentialPhase
    fun_prop
  simp_rw [he]
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun m _ => ht n m))]
  apply sum_congr rfl
  intro n _
  rw [integral_finsetSum _ (fun m _ => ht n m)]
  apply sum_congr rfl
  intro m _
  rw [integral_const_mul]

/-- Actual mean-square integral for arbitrary coefficients and separated real
frequencies. The logarithmic cost is proved; no mean-value premise is assumed. -/
theorem separated_frequency_mean_value (S : Finset ι) (ω : ι → ℝ) (c : ι → ℂ)
    {δ L a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hω : ∀ i ∈ S, |ω i| ≤ L)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |ω i - ω j|) :
    (∫ t in Set.Icc a b, ‖exponentialPolynomial S ω c t‖ ^ 2) ≤
      ((b-a) + 4 * δ⁻¹ * (1 + Real.log ⌊2*L/δ⌋₊)) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  classical
  let k := fun n m : ι => if n = m then b-a else 2 / |ω n - ω m|
  have hk : ∀ n ∈ S, ∀ m ∈ S, 0 ≤ k n m := by
    intro n _ m _
    dsimp [k]
    split_ifs <;> positivity
  have hsym : ∀ n ∈ S, ∀ m ∈ S, k n m = k m n := by
    intro n _ m _
    simp only [k, eq_comm, abs_sub_comm]
  have hrow : ∀ n ∈ S, (∑ m ∈ S, k n m) ≤
      (b-a) + 4 * δ⁻¹ * (1 + Real.log ⌊2*L/δ⌋₊) := by
    intro n hn
    rw [← sum_erase_add _ _ hn]
    have he : (∑ m ∈ S.erase n, k n m) = 2 * ∑ m ∈ S.erase n, |ω n - ω m|⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      simp only [k, ite_eq_right (Ne.symm (mem_erase.mp hm).1), div_eq_mul_inv]
    rw [he]
    have hh := reciprocal_frequency_row S ω hδ hω hsep hn
    simp only [k, ite_true]
    linarith
  have hgram (n m : ι) (hn : n ∈ S) (hm : m ∈ S) :
      ‖∫ t in Set.Icc a b, exponentialPhase (ω n) t * conj (exponentialPhase (ω m) t)‖ ≤ k n m := by
    by_cases he : n = m
    · subst m
      simp only [k, ite_true, Complex.mul_conj', exponentialPhase_norm, one_pow, Complex.ofReal_one]
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab), Complex.real_smul, mul_one]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
    · have hne : ω n - ω m ≠ 0 := abs_pos.mp (hδ.trans_le (hsep n hn m hm he))
      simp_rw [exponentialPhase_pair]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
      simpa only [k, ite_eq_right he, exponentialPhase] using
        GuthMaynard.Improvement.dirichlet_oscillatory_integral (a := a) (b := b) hne
  have hreal : ‖∫ t in Set.Icc a b, (‖exponentialPolynomial S ω c t‖ ^ 2 : ℂ)‖ =
      ∫ t in Set.Icc a b, ‖exponentialPolynomial S ω c t‖ ^ 2 := by
    simp only [← Complex.ofReal_pow]
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  rw [← hreal, exponential_gram]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ S, ∑ m ∈ S, ‖c n‖ * ‖c m‖ * k n m := by
      apply sum_le_sum
      intro n hn
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro m hm
      rw [norm_mul, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hgram n m hn hm)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := GuthMaynard.Improvement.finite_symmetric_row_bound S (fun n => ‖c n‖) k hk hsym hrow

theorem exponentialPolynomial_derivative (S : Finset ι) (ω : ι → ℝ) (c : ι → ℂ) (t : ℝ) :
    HasDerivAt (exponentialPolynomial S ω c)
      (exponentialPolynomial S ω (fun n => c n * (Complex.I * (ω n : ℂ))) t) t := by
  unfold exponentialPolynomial
  apply HasDerivAt.fun_sum
  intro n _
  have hd : HasDerivAt (fun x : ℝ => Complex.I * (ω n : ℂ) * (x : ℂ))
      (Complex.I * (ω n : ℂ)) t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (Complex.I * (ω n : ℂ))
  convert (hd.cexp).const_mul (c n) using 1
  all_goals simp only [exponentialPhase]
  all_goals ring

theorem frequency_cost_nonneg {δ D L : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D) :
    0 ≤ D + 4 * δ⁻¹ * (1 + Real.log ⌊2*L/δ⌋₊) := by
  by_cases hN : ⌊2*L/δ⌋₊ = 0
  · simp only [hN, Nat.cast_zero, Real.log_zero, add_zero]
    positivity
  · have hN1 : (1 : ℝ) ≤ ⌊2*L/δ⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    have hl := Real.log_nonneg hN1
    positivity

/-- Actual values on any one-separated ordinate set, with arbitrary complex
coefficients. All integral and derivative estimates are discharged. -/
theorem separated_frequency_discrete_mean_value (S : Finset ι) (ω : ι → ℝ) (c : ι → ℂ)
    {δ L T t₀ : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hω : ∀ i ∈ S, |ω i| ≤ L)
    (hfreq : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |ω i - ω j|)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    (∑ t ∈ W, ‖exponentialPolynomial S ω c t‖ ^ 2) ≤
      (2 + L ^ 2) * (T+1 + 4 * δ⁻¹ * (1 + Real.log ⌊2*L/δ⌋₊)) *
        ∑ n ∈ S, ‖c n‖ ^ 2 := by
  let D := exponentialPolynomial S ω c
  let c' := fun n => c n * (Complex.I * (ω n : ℂ))
  let D' := exponentialPolynomial S ω c'
  let J := Set.Icc t₀ (t₀+T+1)
  let C := T+1 + 4 * δ⁻¹ * (1 + Real.log ⌊2*L/δ⌋₊)
  let E := ∑ n ∈ S, ‖c n‖ ^ 2
  have hC : 0 ≤ C := frequency_cost_nonneg hδ (by linarith)
  have hc : Continuous D := exponentialPolynomial_continuous S ω c
  have hc' : Continuous D' := exponentialPolynomial_continuous S ω c'
  have hd : ∀ t, HasDerivAt (fun x => D x ^ 2) (2 * D t * D' t) t := by
    intro t
    convert (exponentialPolynomial_derivative S ω c t).pow 2 using 1
    simp [D, D', c', pow_one]
  have hf : IntegrableOn (fun t => D t ^ 2) J := (hc.pow 2).continuousOn.integrableOn_Icc
  have hi : IntegrableOn (fun t => 2 * D t * D' t) J :=
    ((continuous_const.mul hc).mul hc').continuousOn.integrableOn_Icc
  have hs : Pairwise (fun t u : W => (1 : ℝ) ≤ |(t : ℝ) - (u : ℝ)|) := by
    intro t u hne
    exact hsep t t.property u u.property (fun he => hne (Subtype.ext he))
  have hsub : ∀ t : W, Set.Ioc (t : ℝ) ((t : ℝ)+1) ⊆ J := by
    intro t x hx
    have ht := hW t t.property
    exact ⟨by linarith [ht.1, hx.1], by linarith [ht.2, hx.2]⟩
  have hh := GuthMaynard.Improvement.sampling_separated_norm
    (fun t : W => (t : ℝ)) (by norm_num : (0 : ℝ) < 1) hd hs hsub hf hi
  simp only [inv_one, one_mul, norm_pow] at hh
  rw [Finset.sum_coe_sort W (fun t => ‖D t‖ ^ 2)] at hh
  have hD : IntegrableOn (fun t => ‖D t‖ ^ 2) J := (hc.norm.pow 2).continuousOn.integrableOn_Icc
  have hD' : IntegrableOn (fun t => ‖D' t‖ ^ 2) J := (hc'.norm.pow 2).continuousOn.integrableOn_Icc
  have hcross : (∫ t in J, ‖2 * D t * D' t‖) ≤
      (∫ t in J, ‖D t‖ ^ 2) + (∫ t in J, ‖D' t‖ ^ 2) := by
    rw [← integral_add hD hD']
    apply integral_mono hi.norm (hD.add hD')
    intro t
    simp only [norm_mul, Complex.norm_ofNat, Pi.add_apply]
    nlinarith [sq_nonneg (‖D t‖ - ‖D' t‖)]
  have hb : (∫ t in J, ‖D t‖ ^ 2) ≤ C * E := by
    simpa [J, D, C, E, show t₀+T+1-t₀ = T+1 by ring] using separated_frequency_mean_value S ω c hδ
      (show t₀ ≤ t₀+T+1 by linarith) hω hfreq
  have henergy : (∑ n ∈ S, ‖c' n‖ ^ 2) ≤ L ^ 2 * E := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    simp only [c', norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have hl : |ω n| ^ 2 ≤ L ^ 2 := (sq_le_sq₀ (abs_nonneg _) hL).mpr (hω n hn)
    nlinarith [mul_le_mul_of_nonneg_left hl (sq_nonneg ‖c n‖)]
  have hb' : (∫ t in J, ‖D' t‖ ^ 2) ≤ C * (L ^ 2 * E) := by
    have hm := separated_frequency_mean_value S ω c' hδ
      (show t₀ ≤ t₀+T+1 by linarith) hω hfreq
    have hm' : (∫ t in J, ‖D' t‖ ^ 2) ≤ C * (∑ n ∈ S, ‖c' n‖ ^ 2) := by
      simpa [J, D', C, show t₀+T+1-t₀ = T+1 by ring] using hm
    exact hm'.trans (mul_le_mul_of_nonneg_left henergy hC)
  change (∑ t ∈ W, ‖D t‖ ^ 2) ≤ (2 + L ^ 2) * C * E
  nlinarith

end Montgomery.RationalMoment

#print axioms Montgomery.RationalMoment.separated_frequency_mean_value
#print axioms Montgomery.RationalMoment.separated_frequency_discrete_mean_value
