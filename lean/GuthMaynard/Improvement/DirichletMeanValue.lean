import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ComplexConjugate
namespace GuthMaynard.Improvement

/-- Literal positive-integer Dirichlet phase, with no Fourier normalization hidden. -/
def dirichletPhase (n : ℕ) (t : ℝ) : ℂ := Complex.exp (Complex.I * (Real.log n : ℂ) * t)

def finiteDirichletPolynomial (X : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, c n * dirichletPhase n t

theorem dirichlet_log_gap {m n X : ℕ} (hm : 0 < m) (hmn : m < n) (hnX : n ≤ X) :
    ((n-m:ℕ):ℝ)/(X:ℝ) ≤ Real.log n - Real.log m := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hmn' : (m:ℝ) < n := by exact_mod_cast hmn
  have hn0 : (0:ℝ) < n := lt_trans hm0 hmn'
  have hX : (n:ℝ) ≤ X := by exact_mod_cast hnX
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hm0)
  rw [Real.log_div (ne_of_gt hn0) (ne_of_gt hm0),inv_div] at hh
  have hcast : ((n-m:ℕ):ℝ) = (n:ℝ)-m := Nat.cast_sub hmn.le
  rw [hcast]
  calc
    ((n:ℝ)-m)/X ≤ ((n:ℝ)-m)/n := div_le_div_of_nonneg_left (by linarith) hn0 hX
    _ = 1-(m:ℝ)/n := by field_simp
    _ ≤ _ := hh

theorem dirichletPhase_norm (n : ℕ) (t : ℝ) : ‖dirichletPhase n t‖ = 1 := by
  simp only [dirichletPhase,Complex.norm_exp,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,one_mul,zero_add,Real.exp_zero]

theorem dirichlet_oscillatory_integral {ω a b : ℝ} (hω : ω ≠ 0) :
    ‖∫ t in a..b, Complex.exp (Complex.I * (ω:ℂ) * t)‖ ≤ 2/|ω| := by
  have hc : Complex.I * (ω:ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hω)
  rw [integral_exp_mul_complex hc,norm_div,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg ω)
  have hn (t : ℝ) : ‖Complex.exp (Complex.I * (ω:ℂ) * t)‖ = 1 := by
    simp [Complex.norm_exp]
  simpa only [hn,one_add_one_eq_two] using norm_sub_le (Complex.exp (Complex.I*(ω:ℂ)*b)) (Complex.exp (Complex.I*(ω:ℂ)*a))


/-- Each side of a reciprocal integer-distance row injects into the harmonic sum. -/
theorem dirichlet_distance_side (X n : ℕ) (hn : n ≤ X) (S : Finset ℕ)
    (_hS : S ⊆ Finset.Icc 1 X) (hside : ∀ m ∈ S, m < n) :
    (∑ m ∈ S, ((n-m:ℕ):ℝ)⁻¹) ≤ (harmonic X:ℝ) := by
  have hinj : Set.InjOn (fun m => n-m) S := by
    intro x hx y hy he
    have hx' := hside x hx
    have hy' := hside y hy
    dsimp at he
    omega
  have himage : S.image (fun m => n-m) ⊆ Finset.Icc 1 X := by
    intro k hk
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hk
    have hh := hside m hm
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [← Finset.sum_image (f := fun k : ℕ => (k:ℝ)⁻¹) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)

theorem dirichlet_distance_other_side (X n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 X) (hside : ∀ m ∈ S, n < m) :
    (∑ m ∈ S, ((m-n:ℕ):ℝ)⁻¹) ≤ (harmonic X:ℝ) := by
  have hinj : Set.InjOn (fun m => m-n) S := by
    intro x hx y hy he
    have hx' := hside x hx
    have hy' := hside y hy
    dsimp at he
    omega
  have himage : S.image (fun m => m-n) ⊆ Finset.Icc 1 X := by
    intro k hk
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hk
    have hh := hside m hm
    have hmX := (Finset.mem_Icc.mp (hS hm)).2
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [← Finset.sum_image (f := fun k : ℕ => (k:ℝ)⁻¹) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)


theorem dirichlet_harmonic_row {X n : ℕ} (hn : n ∈ Finset.Icc 1 X) :
    (∑ m ∈ (Finset.Icc 1 X).erase n, (|(n:ℝ)-m|)⁻¹) ≤ 2*(1+Real.log X) := by
  let S := (Finset.Icc 1 X).erase n
  have hleft := dirichlet_distance_side X n (Finset.mem_Icc.mp hn).2
    (S.filter (fun m => m<n))
    (fun m hm => Finset.mem_of_mem_erase (Finset.mem_filter.mp hm).1)
    (fun m hm => (Finset.mem_filter.mp hm).2)
  have hright := dirichlet_distance_other_side X n (S.filter (fun m => ¬m<n))
    (fun m hm => Finset.mem_of_mem_erase (Finset.mem_filter.mp hm).1)
    (fun m hm => by
      have hne := (Finset.mem_erase.mp (Finset.mem_filter.mp hm).1).1
      have hnot := (Finset.mem_filter.mp hm).2
      omega)
  have heleft : (∑ m ∈ S.filter (fun m => m<n), (|(n:ℝ)-m|)⁻¹) =
      ∑ m ∈ S.filter (fun m => m<n), ((n-m:ℕ):ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmn := (Finset.mem_filter.mp hm).2
    rw [Nat.cast_sub hmn.le,abs_of_nonneg (by exact_mod_cast (sub_nonneg.mpr (show (m:ℝ) ≤ n by exact_mod_cast hmn.le)))]
  have heright : (∑ m ∈ S.filter (fun m => ¬m<n), (|(n:ℝ)-m|)⁻¹) =
      ∑ m ∈ S.filter (fun m => ¬m<n), ((m-n:ℕ):ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro m hm
    have hnm : n ≤ m := Nat.le_of_not_gt (Finset.mem_filter.mp hm).2
    rw [Nat.cast_sub hnm,abs_of_nonpos (by exact_mod_cast (sub_nonpos.mpr (show (n:ℝ) ≤ m by exact_mod_cast hnm)))]
    congr 1
    ring
  have he := Finset.sum_filter_add_sum_filter_not S (fun m => m<n) (fun m => (|(n:ℝ)-m|)⁻¹)
  change (∑ m ∈ S, (|(n:ℝ)-m|)⁻¹) ≤ _
  rw [← he,heleft,heright]
  nlinarith [harmonic_le_one_add_log X]


theorem dirichletPhase_continuous (n : ℕ) : Continuous (dirichletPhase n) := by
  unfold dirichletPhase
  fun_prop

theorem finiteDirichletPolynomial_continuous (X : ℕ) (c : ℕ → ℂ) :
    Continuous (finiteDirichletPolynomial X c) := by
  unfold finiteDirichletPolynomial dirichletPhase
  fun_prop

theorem dirichletPhase_mul_conj (n m : ℕ) (t : ℝ) :
    dirichletPhase n t * conj (dirichletPhase m t) =
      Complex.exp (Complex.I*((Real.log n-Real.log m:ℝ):ℂ)*t) := by
  unfold dirichletPhase
  rw [← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_sub]
  ring

theorem dirichlet_off_diagonal {X n m : ℕ} (hn : n ∈ Finset.Icc 1 X)
    (hm : m ∈ Finset.Icc 1 X) (hne : n ≠ m) (a b : ℝ) :
    ‖∫ t in a..b, dirichletPhase n t * conj (dirichletPhase m t)‖ ≤
      2*(X:ℝ)/|(n:ℝ)-m| := by
  have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hX0 : (0:ℝ)<X := by exact_mod_cast (lt_of_lt_of_le hn0 (Finset.mem_Icc.mp hn).2)
  have hdist : 0 < |(n:ℝ)-m| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
  have hgap : |(n:ℝ)-m|/(X:ℝ) ≤ |Real.log n-Real.log m| := by
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · have hh := dirichlet_log_gap hn0 hnm (Finset.mem_Icc.mp hm).2
      rw [Nat.cast_sub hnm.le] at hh
      rw [abs_of_neg (by exact_mod_cast (sub_neg.mpr (show (n:ℝ) < m by exact_mod_cast hnm))),abs_sub_comm]
      calc
        _ = ((m:ℝ)-n)/X := by ring
        _ ≤ Real.log m-Real.log n := hh
        _ ≤ _ := le_abs_self _
    · have hh := dirichlet_log_gap hm0 hmn (Finset.mem_Icc.mp hn).2
      rw [Nat.cast_sub hmn.le] at hh
      rw [abs_of_pos (by exact_mod_cast (sub_pos.mpr (show (m:ℝ) < n by exact_mod_cast hmn)))]
      exact hh.trans (le_abs_self _)
  have hω : Real.log n-Real.log m ≠ 0 := by
    have hh := lt_of_lt_of_le (div_pos hdist hX0) hgap
    exact (abs_pos.mp hh)
  simp_rw [dirichletPhase_mul_conj]
  calc
    _ ≤ 2/|Real.log n-Real.log m| := dirichlet_oscillatory_integral hω
    _ ≤ 2/(|(n:ℝ)-m|/X) := div_le_div_of_nonneg_left (by norm_num) (div_pos hdist hX0) hgap
    _ = _ := by field_simp


/-- Elementary finite Schur estimate, with actual row bounds exposed only in this helper. -/
theorem finite_symmetric_row_bound {ι : Type*} (S : Finset ι) (v : ι → ℝ)
    (k : ι → ι → ℝ) (hk : ∀ n ∈ S, ∀ m ∈ S, 0 ≤ k n m)
    (hsym : ∀ n ∈ S, ∀ m ∈ S, k n m = k m n) {B : ℝ}
    (hrow : ∀ n ∈ S, (∑ m ∈ S, k n m) ≤ B) :
    (∑ n ∈ S, ∑ m ∈ S, v n*v m*k n m) ≤ B*(∑ n ∈ S, (v n)^2) := by
  have hterm : (∑ n ∈ S, ∑ m ∈ S, v n*v m*k n m) ≤
      (∑ n ∈ S, ∑ m ∈ S, ((v n)^2*k n m+(v m)^2*k n m)/2) := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro m hm
    have hh := mul_nonneg (sq_nonneg (v n-v m)) (hk n hn m hm)
    nlinarith
  have hswap : (∑ n ∈ S, ∑ m ∈ S, (v m)^2*k n m) =
      ∑ n ∈ S, ∑ m ∈ S, (v n)^2*k n m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [hsym m hm n hn]
  calc
    _ ≤ _ := hterm
    _ = ∑ n ∈ S, (v n)^2*(∑ m ∈ S, k n m) := by
      simp only [div_eq_mul_inv,add_mul,Finset.sum_add_distrib,← Finset.sum_mul]
      rw [hswap]
      simp only [Finset.mul_sum]
      ring
    _ ≤ ∑ n ∈ S, (v n)^2*B := Finset.sum_le_sum (fun n hn =>
      mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring


/-- Actual integrability of the squared finite Dirichlet polynomial on every compact interval. -/
theorem finiteDirichletPolynomial_integrable (X : ℕ) (c : ℕ → ℂ) (a b : ℝ) :
    IntegrableOn (fun t => ‖finiteDirichletPolynomial X c t‖^2) (Set.Icc a b) :=
  ((finiteDirichletPolynomial_continuous X c).norm.pow 2).continuousOn.integrableOn_Icc

/-- Exact finite Gram expansion on the actual interval. -/
theorem finiteDirichletPolynomial_gram (X : ℕ) (c : ℕ → ℂ) (a b : ℝ) :
    (∫ t in Set.Icc a b, (‖finiteDirichletPolynomial X c t‖^2:ℂ)) =
      ∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
        (c n*conj (c m))*(∫ t in Set.Icc a b, dirichletPhase n t*conj (dirichletPhase m t)) := by
  have he (t : ℝ) : (‖finiteDirichletPolynomial X c t‖^2:ℂ) =
      ∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
        (c n*conj (c m))*(dirichletPhase n t*conj (dirichletPhase m t)) := by
    rw [← Complex.mul_conj']
    simp only [finiteDirichletPolynomial,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    ring
  have ht (n m : ℕ) : IntegrableOn
      (fun t => (c n*conj (c m))*(dirichletPhase n t*conj (dirichletPhase m t))) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    unfold dirichletPhase
    fun_prop
  simp_rw [he]
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun m _ => ht n m))]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_finsetSum _ (fun m _ => ht n m)]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_const_mul]

/-- Elementary Dirichlet mean value with an absolute logarithmic loss.
The coefficients and interval location are arbitrary. -/
theorem dirichlet_mean_value (X : ℕ) (c : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Set.Icc a b, ‖finiteDirichletPolynomial X c t‖^2) ≤
      ((b-a)+4*(X:ℝ)*(1+Real.log X))*(∑ n ∈ Finset.Icc 1 X, ‖c n‖^2) := by
  let S := Finset.Icc 1 X
  let k := fun n m : ℕ => if n=m then b-a else 2*(X:ℝ)/|(n:ℝ)-m|
  have hk : ∀ n ∈ S, ∀ m ∈ S, 0 ≤ k n m := by
    intro n _ m _
    dsimp [k]
    split_ifs <;> positivity
  have hsym : ∀ n ∈ S, ∀ m ∈ S, k n m=k m n := by
    intro n _ m _
    simp only [k,eq_comm,abs_sub_comm]
  have hrow : ∀ n ∈ S, (∑ m ∈ S, k n m) ≤ (b-a)+4*(X:ℝ)*(1+Real.log X) := by
    intro n hn
    rw [← Finset.sum_erase_add _ _ hn]
    have he : (∑ m ∈ S.erase n, k n m) =
        2*(X:ℝ)*(∑ m ∈ S.erase n, (|(n:ℝ)-m|)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hne : n ≠ m := Ne.symm (Finset.mem_erase.mp hm).1
      simp only [k,ite_eq_right hne,div_eq_mul_inv]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (dirichlet_harmonic_row hn) (by positivity : 0 ≤ 2*(X:ℝ))
    simp only [k,ite_true]
    nlinarith
  have hgram (n m : ℕ) (hn : n ∈ S) (hm : m ∈ S) :
      ‖∫ t in Set.Icc a b, dirichletPhase n t*conj (dirichletPhase m t)‖ ≤ k n m := by
    by_cases he : n=m
    · subst m
      simp only [k,ite_true,Complex.mul_conj',dirichletPhase_norm,one_pow,Complex.ofReal_one]
      simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab),Complex.real_smul,mul_one]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)]
    · rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
      simpa only [k,ite_eq_right he] using dirichlet_off_diagonal hn hm he a b
  have hexpand := finiteDirichletPolynomial_gram X c a b
  have hreal : ‖∫ t in Set.Icc a b, (‖finiteDirichletPolynomial X c t‖^2:ℂ)‖ =
      ∫ t in Set.Icc a b, ‖finiteDirichletPolynomial X c t‖^2 := by
    simp only [← Complex.ofReal_pow]
    rw [integral_complex_ofReal,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  rw [← hreal,hexpand]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ S, ∑ m ∈ S, ‖c n‖*‖c m‖*k n m := by
      apply Finset.sum_le_sum
      intro n hn
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul,norm_mul,RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hgram n m hn hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := finite_symmetric_row_bound S (fun n => ‖c n‖) k hk hsym hrow

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.dirichlet_log_gap
#print axioms GuthMaynard.Improvement.dirichletPhase_norm
#print axioms GuthMaynard.Improvement.dirichlet_oscillatory_integral

#print axioms GuthMaynard.Improvement.dirichlet_distance_side
#print axioms GuthMaynard.Improvement.dirichlet_distance_other_side

#print axioms GuthMaynard.Improvement.dirichlet_harmonic_row

#print axioms GuthMaynard.Improvement.dirichletPhase_continuous
#print axioms GuthMaynard.Improvement.finiteDirichletPolynomial_continuous
#print axioms GuthMaynard.Improvement.dirichletPhase_mul_conj
#print axioms GuthMaynard.Improvement.dirichlet_off_diagonal

#print axioms GuthMaynard.Improvement.finite_symmetric_row_bound

#print axioms GuthMaynard.Improvement.finiteDirichletPolynomial_integrable
#print axioms GuthMaynard.Improvement.finiteDirichletPolynomial_gram
#print axioms GuthMaynard.Improvement.dirichlet_mean_value
