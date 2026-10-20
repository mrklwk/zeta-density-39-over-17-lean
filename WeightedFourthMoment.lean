module
public import Mathlib

@[expose] public section

/-! Elementary mean-zero fourth-moment contraction. This is a proved ingredient
for a possible divisor-weight proof of the rational coefficient estimate.
The multidimensional and arithmetic assembly is not asserted here. -/
set_option autoImplicit false
noncomputable section
open Finset
open scoped ComplexConjugate
namespace Montgomery.RationalMoment

theorem fourth_power_with_linear_term (a z : ℂ) {E : ℝ}
    (hE : ‖z‖ ^ 2 ≤ E) :
    ‖a+z‖ ^ 4 ≤ (‖a‖ ^ 2 + 4*E)^2 + 4*‖a‖^2*(conj a*z).re := by
  have hE0 : 0 ≤ E := (sq_nonneg _).trans hE
  have hr : (conj a*z).re ^ 2 ≤ ‖a‖ ^ 2 * ‖z‖ ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_conj, mul_pow, ← pow_two]
      using Complex.re_sq_le_normSq (conj a*z)
  have hid : ‖a+z‖ ^ 2 = ‖a‖ ^ 2 + 2*(conj a*z).re + ‖z‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hid4 : ‖a+z‖ ^ 4 = (‖a‖ ^ 2 + 2*(conj a*z).re + ‖z‖ ^ 2)^2 := by
    rw [show ‖a+z‖ ^ 4 = (‖a+z‖ ^ 2)^2 by ring, hid]
  have hE2 := (sq_le_sq₀ (sq_nonneg ‖z‖) hE0).mpr hE
  have hm := mul_le_mul_of_nonneg_left hE (sq_nonneg ‖a‖)
  nlinarith [sq_nonneg ((conj a*z).re - ‖z‖^2)]

/-- A finite probability average of a mean-zero perturbation has a fourth
moment controlled by its uniform square bound. No Fourier estimate is assumed. -/
theorem mean_zero_fourth_moment {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (f : ι → ℂ) (a : ℂ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hsum : ∑ x ∈ S, w x = 1)
    (hmean : ∑ x ∈ S, (w x : ℂ)*f x = 0) {E : ℝ}
    (hE : ∀ x ∈ S, ‖f x‖^2 ≤ E) :
    (∑ x ∈ S, w x * ‖a+f x‖^4) ≤ (‖a‖^2 + 4*E)^2 := by
  have hlinear : (∑ x ∈ S, w x * (conj a*f x).re) = 0 := by
    calc
      _ = (∑ x ∈ S, (w x : ℂ)*(conj a*f x)).re := by
        rw [Complex.re_sum]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ = (conj a * (∑ x ∈ S, (w x : ℂ)*f x)).re := by
        congr 1
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hmean, mul_zero, Complex.zero_re]
  calc
    _ ≤ ∑ x ∈ S, w x * ((‖a‖^2+4*E)^2 + 4*‖a‖^2*(conj a*f x).re) :=
      sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left
        (fourth_power_with_linear_term a (f x) (hE x hx)) (hw x hx))
    _ = (∑ x ∈ S, w x)*(‖a‖^2+4*E)^2 +
        4*‖a‖^2*(∑ x ∈ S, w x*(conj a*f x).re) := by
      simp only [mul_add, sum_add_distrib, sum_mul, mul_sum]
      congr 1
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [hsum, hlinear]; ring

/-- Weighted Cauchy--Schwarz supplies a pointwise square bound from a finite
reciprocal-square budget. -/
theorem weighted_character_square {ι : Type*} (A : Finset ι)
    (c χ : ι → ℂ) (v : ι → ℝ) (hv : ∀ n ∈ A, v n ≠ 0)
    (hχ : ∀ n ∈ A, ‖χ n‖ ≤ 1) {K : ℝ}
    (hK : (∑ n ∈ A, (v n)⁻¹ ^ 2) ≤ K) :
    ‖∑ n ∈ A, c n*χ n‖ ^ 2 ≤ K * ∑ n ∈ A, (v n)^2*‖c n‖^2 := by
  have hn : ‖∑ n ∈ A, c n*χ n‖ ≤ ∑ n ∈ A, ‖c n‖ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hχ n hn) (norm_nonneg _)).trans_eq (mul_one _)
  have hcs := sum_mul_sq_le_sq_mul_sq A (fun n => v n*‖c n‖) (fun n => (v n)⁻¹)
  have he : (∑ n ∈ A, (v n*‖c n‖)*(v n)⁻¹) = ∑ n ∈ A, ‖c n‖ := by
    apply sum_congr rfl
    intro n hn
    field_simp [hv n hn]
  rw [he] at hcs
  simp only [mul_pow] at hcs
  have hm := mul_le_mul_of_nonneg_left hK
    (show 0 ≤ ∑ n ∈ A, (v n)^2*‖c n‖^2 from
      sum_nonneg (fun n _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hn2 := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg (fun _ _ => norm_nonneg _))).mpr hn
  nlinarith

/-- One-coordinate weighted fourth moment for mean-zero bounded characters.
The analytic fourth-moment conclusion is proved, rather than assumed. -/
theorem weighted_character_fourth_moment {ι τ : Type*}
    (A : Finset ι) (S : Finset τ) (w : τ → ℝ) (χ : ι → τ → ℂ)
    (c : ι → ℂ) (a : ℂ) (v : ι → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hsum : ∑ x ∈ S, w x = 1)
    (hmean : ∀ n ∈ A, ∑ x ∈ S, (w x : ℂ)*χ n x = 0)
    (hv : ∀ n ∈ A, v n ≠ 0) (hχ : ∀ n ∈ A, ∀ x ∈ S, ‖χ n x‖ ≤ 1)
    {K : ℝ} (hK : (∑ n ∈ A, (v n)⁻¹ ^ 2) ≤ K) :
    (∑ x ∈ S, w x * ‖a + ∑ n ∈ A, c n*χ n x‖^4) ≤
      (‖a‖^2 + 4*K*(∑ n ∈ A, (v n)^2*‖c n‖^2))^2 := by
  have hm : (∑ x ∈ S, (w x : ℂ)*(∑ n ∈ A, c n*χ n x)) = 0 := by
    simp only [mul_sum]
    rw [sum_comm]
    calc
      _ = ∑ n ∈ A, c n*(∑ x ∈ S, (w x : ℂ)*χ n x) := by
        apply sum_congr rfl
        intro n _
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ = 0 := sum_eq_zero (fun n hn => by rw [hmean n hn, mul_zero])
  have hh := mean_zero_fourth_moment S w (fun x => ∑ n ∈ A, c n*χ n x) a hw hsum hm
    (fun x hx => weighted_character_square A c (fun n => χ n x) v hv (fun n hn => hχ n hn x hx) hK)
  simpa only [mul_assoc] using hh

/-- Weighted Cauchy--Schwarz converts two fourth-moment estimates to the
mixed second-square estimate used in the product argument. -/
theorem mixed_fourth_bound {τ : Type*} (S : Finset τ) (w : τ → ℝ)
    (f g : τ → ℂ) (hw : ∀ x ∈ S, 0 ≤ w x) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : (∑ x ∈ S, w x * ‖f x‖^4) ≤ A^2)
    (hg : (∑ x ∈ S, w x * ‖g x‖^4) ≤ B^2) :
    (∑ x ∈ S, w x * ‖f x‖^2 * ‖g x‖^2) ≤ A*B := by
  have hc := sum_mul_sq_le_sq_mul_sq S
    (fun x => Real.sqrt (w x)*‖f x‖^2) (fun x => Real.sqrt (w x)*‖g x‖^2)
  have he (x : τ) (hx : x ∈ S) :
      (Real.sqrt (w x)*‖f x‖^2)*(Real.sqrt (w x)*‖g x‖^2) = w x*‖f x‖^2*‖g x‖^2 := by
    calc
      _ = (Real.sqrt (w x))^2*‖f x‖^2*‖g x‖^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hw x hx)]
  have hef (x : τ) (hx : x ∈ S) : (Real.sqrt (w x)*‖f x‖^2)^2 = w x*‖f x‖^4 := by
    rw [mul_pow, Real.sq_sqrt (hw x hx)]
    ring
  have heg (x : τ) (hx : x ∈ S) : (Real.sqrt (w x)*‖g x‖^2)^2 = w x*‖g x‖^4 := by
    rw [mul_pow, Real.sq_sqrt (hw x hx)]
    ring
  rw [sum_congr rfl he, sum_congr rfl hef, sum_congr rfl heg] at hc
  have hfg := mul_le_mul hf hg
    (sum_nonneg (fun x hx => mul_nonneg (hw x hx) (pow_nonneg (norm_nonneg _) _))) (sq_nonneg A)
  have hnonneg : 0 ≤ ∑ x ∈ S, w x*‖f x‖^2*‖g x‖^2 :=
    sum_nonneg (fun x hx => mul_nonneg (mul_nonneg (hw x hx) (sq_nonneg _)) (sq_nonneg _))
  apply (sq_le_sq₀ hnonneg (mul_nonneg hA hB)).mp
  nlinarith

/-- A finite weighted fourth-moment bound tensorizes with no loss of constant.
The two one-coordinate bounds are premises; the product bound is proved. -/
theorem tensorize_fourth_bound {ι κ τ υ : Type*}
    (A : Finset ι) (B : Finset κ) (X : Finset τ) (Y : Finset υ)
    (wx : τ → ℝ) (wy : υ → ℝ) (u : ι → ℝ) (v : κ → ℝ)
    (χ : ι → τ → ℂ) (ψ : κ → υ → ℂ)
    (hwy : ∀ y ∈ Y, 0 ≤ wy y) (hu : ∀ i ∈ A, 0 ≤ u i) (hv : ∀ j ∈ B, 0 ≤ v j)
    (hχ : ∀ a : ι → ℂ, (∑ x ∈ X, wx x * ‖∑ i ∈ A, a i*χ i x‖^4) ≤
      (∑ i ∈ A, u i*‖a i‖^2)^2)
    (hψ : ∀ b : κ → ℂ, (∑ y ∈ Y, wy y * ‖∑ j ∈ B, b j*ψ j y‖^4) ≤
      (∑ j ∈ B, v j*‖b j‖^2)^2)
    (c : ι → κ → ℂ) :
    (∑ y ∈ Y, ∑ x ∈ X, wy y * wx x *
      ‖∑ i ∈ A, (∑ j ∈ B, c i j*ψ j y)*χ i x‖^4) ≤
      (∑ i ∈ A, ∑ j ∈ B, u i*v j*‖c i j‖^2)^2 := by
  let F := fun i y => ∑ j ∈ B, c i j*ψ j y
  let E := fun i => ∑ j ∈ B, v j*‖c i j‖^2
  have hE (i : ι) : 0 ≤ E i := sum_nonneg (fun j hj => mul_nonneg (hv j hj) (sq_nonneg _))
  have hm (i l : ι) : (∑ y ∈ Y, wy y*‖F i y‖^2*‖F l y‖^2) ≤ E i*E l :=
    mixed_fourth_bound Y wy (F i) (F l) hwy (hE i) (hE l) (hψ (c i)) (hψ (c l))
  have ht : (∑ y ∈ Y, ∑ x ∈ X, wy y*wx x*‖∑ i ∈ A, F i y*χ i x‖^4) ≤
      ∑ y ∈ Y, wy y*(∑ i ∈ A, u i*‖F i y‖^2)^2 := by
    apply sum_le_sum
    intro y hy
    simpa only [mul_sum, mul_assoc] using mul_le_mul_of_nonneg_left
      (hχ (fun i => F i y)) (hwy y hy)
  have hexpand : (∑ y ∈ Y, wy y*(∑ i ∈ A, u i*‖F i y‖^2)^2) =
      ∑ i ∈ A, ∑ l ∈ A, u i*u l*(∑ y ∈ Y, wy y*‖F i y‖^2*‖F l y‖^2) := by
    simp only [sq, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
    apply sum_congr rfl
    intro l _
    apply sum_congr rfl
    intro y _
    ring
  have hb : (∑ y ∈ Y, wy y*(∑ i ∈ A, u i*‖F i y‖^2)^2) ≤
      (∑ i ∈ A, u i*E i)^2 := by
    rw [hexpand, sq, sum_mul]
    simp only [mul_sum]
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro l hl
    have hh := mul_le_mul_of_nonneg_left (hm i l) (mul_nonneg (hu i hi) (hu l hl))
    rw [← mul_sum]
    convert hh using 1
    ring
  have he : (∑ i ∈ A, u i*E i) = ∑ i ∈ A, ∑ j ∈ B, u i*v j*‖c i j‖^2 := by
    simp only [E, mul_sum, mul_assoc]
  change (∑ y ∈ Y, ∑ x ∈ X, wy y*wx x*‖∑ i ∈ A, F i y*χ i x‖^4) ≤ _
  exact (ht.trans hb).trans_eq (congrArg (fun t : ℝ => t^2) he)

end Montgomery.RationalMoment

#print axioms Montgomery.RationalMoment.fourth_power_with_linear_term
#print axioms Montgomery.RationalMoment.mean_zero_fourth_moment
#print axioms Montgomery.RationalMoment.weighted_character_fourth_moment
#print axioms Montgomery.RationalMoment.tensorize_fourth_bound
