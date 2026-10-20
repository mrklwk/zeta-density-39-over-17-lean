module
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalEndpointSlab
public import GuthMaynard.NativeSource.GuthMaynard.WeylExplicit

@[expose] public section

open Asymptotics Filter Topology
open Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace GuthMaynard.NativeMoment

/-!
# The medium Type-I endpoint consumer

This file closes the one reflected Type-I window left between the direct
endpoint estimate and the finite powering range.  The first lemmas expose
the genuine Bochner-integrability and norm bounds of the common Mellin
integrand.  They are kept separate from the final witness consumer so that
the passage from a source block to a fixed-coefficient reflected polynomial
is visible to the dependency audit.
-/

/-! ## Interval-form reflected polynomials

The endpoint argument cannot use the prefix `1 ≤ m ≤ M`: a dyadic
subblock selected from that prefix could be much shorter than the genuine
dual scale `T / N`.  The following definitions and identity retain an
arbitrary common interval of Fourier modes.  They are the exact Lean
counterpart of first restricting the B-process to its stationary annulus
and only then applying dyadic pigeonholing.
-/

/-- The fixed reflected polynomial on a literal natural interval. -/
noncomputable def typeIReflectedIntervalFixedPolynomial
    (sigma u : ℝ) (L U : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc L U,
    ((((m : ℝ) ^ sigma : ℝ) : ℂ) *
      (m : ℂ) ^ ((u : ℂ) * Complex.I))

/-- The Mellin polynomial on the same interval, before removing the
common physical scale and vertical Mellin phase. -/
noncomputable def typeIReflectedIntervalMellinPolynomial
    (sigma t Q : ℝ) (L U : ℕ) (r : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc L U,
    typeIReflectionScaleFactor sigma t m *
      ((((m : ℝ) * Q : ℝ) : ℂ) *
        (((m : ℝ) * Q : ℝ) : ℂ) ^ ((r : ℂ) * Complex.I))

/-- The literal negative normalized Poisson modes on `L < m ≤ U`. -/
noncomputable def typeINormalizedNegativeInterval
    (sigma t : ℝ) (Q L U : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc L U,
    (Q : ℂ) * typeINormalizedFourier sigma t
      ((Q : ℝ) * (-(m : ℝ)))

/-- The literal positive normalized Poisson modes on `L < m ≤ U`. -/
noncomputable def typeINormalizedPositiveInterval
    (sigma t : ℝ) (Q L U : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc L U,
    (Q : ℂ) * typeINormalizedFourier sigma t
      ((Q : ℝ) * (m : ℝ))

/-- The retained negative prefix is the interval with left endpoint zero.
This small identity is used before splitting the Poisson modes into the
low, stationary, and high ranges. -/
theorem typeINormalizedNegativeModes_eq_zero_interval
    (sigma t : ℝ) (Q M : ℕ) :
    typeINormalizedNegativeModes sigma t Q M =
      typeINormalizedNegativeInterval sigma t Q 0 M := by
  unfold typeINormalizedNegativeModes typeINormalizedNegativeInterval
  congr 1

/-- Exact three-way partition of the retained negative Poisson modes.  In
particular the stationary interval is not replaced by a prefix, so every
later dyadic block remains at the physical dual scale. -/
theorem typeINormalizedNegativeModes_eq_three_intervals
    (sigma t : ℝ) (Q L U M : ℕ) (hLU : L ≤ U) (hUM : U ≤ M) :
    typeINormalizedNegativeModes sigma t Q M =
      typeINormalizedNegativeInterval sigma t Q 0 L +
      typeINormalizedNegativeInterval sigma t Q L U +
      typeINormalizedNegativeInterval sigma t Q U M := by
  rw [typeINormalizedNegativeModes_eq_zero_interval]
  unfold typeINormalizedNegativeInterval
  let f : ℕ → ℂ := fun m =>
    (Q : ℂ) * typeINormalizedFourier sigma t
      ((Q : ℝ) * (-(m : ℝ)))
  have hDisj₁ : Disjoint (Finset.Ioc 0 L) (Finset.Ioc L U) := by
    rw [Finset.disjoint_left]
    intro m hm₁ hm₂
    simp only [Finset.mem_Ioc] at hm₁ hm₂
    omega
  have hDisj₂ : Disjoint (Finset.Ioc 0 U) (Finset.Ioc U M) := by
    rw [Finset.disjoint_left]
    intro m hm₁ hm₂
    simp only [Finset.mem_Ioc] at hm₁ hm₂
    omega
  have hUnion₁ :=
    Finset.Ioc_union_Ioc_eq_Ioc (a := 0) (Nat.zero_le L) hLU
  have hUnion₂ :=
    Finset.Ioc_union_Ioc_eq_Ioc (a := 0) (Nat.zero_le U) hUM
  change (∑ m ∈ Finset.Ioc 0 M, f m) =
    (∑ m ∈ Finset.Ioc 0 L, f m) +
      (∑ m ∈ Finset.Ioc L U, f m) +
      ∑ m ∈ Finset.Ioc U M, f m
  rw [← hUnion₂, Finset.sum_union hDisj₂, ← hUnion₁,
    Finset.sum_union hDisj₁]

/-- The Jacobian and phase in the physical mode rescaling have the exact
power norm `m^(sigma-1)`. -/
theorem norm_typeIReflectionScaleFactor
    {sigma t m : ℝ} (hm : 0 < m) :
    ‖typeIReflectionScaleFactor sigma t m‖ = m ^ (sigma - 1) := by
  unfold typeIReflectionScaleFactor
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hm, Complex.norm_exp,
    Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, mul_one]
  rw [Real.exp_zero, mul_one]
  rw [show sigma * Real.log m = Real.log m * sigma by ring]
  rw [← Real.rpow_def_of_pos hm]
  rw [← Real.rpow_neg_one, ← Real.rpow_add hm]
  congr 1
  ring

/-- Exact removal of the ordinate from an interval-form Mellin
polynomial. -/
theorem typeIReflectedIntervalMellinPolynomial_eq_fixed
    (sigma t Q : ℝ) (L U : ℕ) (r : ℝ) (hQ : 0 < Q) :
    typeIReflectedIntervalMellinPolynomial sigma t Q L U r =
      (Q : ℂ) * (Q : ℂ) ^ ((r : ℂ) * Complex.I) *
        typeIReflectedIntervalFixedPolynomial sigma (t + r) L U := by
  unfold typeIReflectedIntervalMellinPolynomial
    typeIReflectedIntervalFixedPolynomial typeIReflectionScaleFactor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le L)
    (Finset.mem_Ioc.mp hm).1
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hmPos
  have hmComplex : (m : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  have hQComplex : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hmLog : Complex.log (m : ℂ) = (Real.log (m : ℝ) : ℂ) :=
    (Complex.ofReal_log hmReal.le).symm
  have hQLog : Complex.log (Q : ℂ) = (Real.log Q : ℂ) :=
    (Complex.ofReal_log hQ.le).symm
  have hmSigma : ((((m : ℝ) ^ sigma : ℝ) : ℂ)) =
      Complex.exp (((sigma * Real.log (m : ℝ) : ℝ) : ℂ)) := by
    rw [Real.rpow_def_of_pos hmReal, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hMulCast : ((((m : ℝ) * Q : ℝ) : ℂ)) =
      (m : ℂ) * (Q : ℂ) := Complex.ofReal_mul (m : ℝ) Q
  have hMulPow : ((((m : ℝ) * Q : ℝ) : ℂ)) ^ ((r : ℂ) * Complex.I) =
      (m : ℂ) ^ ((r : ℂ) * Complex.I) *
        (Q : ℂ) ^ ((r : ℂ) * Complex.I) := by
    rw [hMulCast]
    exact Complex.mul_cpow_ofReal_nonneg hmReal.le hQ.le _
  rw [hMulPow, hMulCast, hmSigma,
    Complex.cpow_def_of_ne_zero hmComplex,
    Complex.cpow_def_of_ne_zero hQComplex,
    Complex.cpow_def_of_ne_zero hmComplex, hmLog, hQLog]
  field_simp [hmComplex]
  calc
    Complex.exp (((Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) *
          (m : ℂ) *
          Complex.exp (Complex.I * (Real.log (m : ℝ) : ℂ) * (r : ℂ)) =
        (m : ℂ) *
          (Complex.exp (((Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) *
            Complex.exp (Complex.I * (Real.log (m : ℝ) : ℂ) * (r : ℂ))) := by
      ring
    _ = (m : ℂ) * Complex.exp
          ((((Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) +
            Complex.I * (Real.log (m : ℝ) : ℂ) * (r : ℂ)) := by
      rw [Complex.exp_add]
    _ = (m : ℂ) * Complex.exp
          (Complex.I * (Real.log (m : ℝ) : ℂ) * ((t + r : ℝ) : ℂ)) := by
      congr 2
      push_cast
      ring

/-- Exact B-process assembly for a common interval `L < m ≤ U`.  The
common reflection interval is chosen from the extreme supports of the
interval, so every mode has the same oscillatory kernel. -/
theorem sum_typeIDyadicPhysicalIntegral_interval_eq_reflectedMellin
    {sigma t Q : ℝ} {L U : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hLU : L < U) :
    (∑ m ∈ Finset.Ioc L U,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q) := by
  let S := Finset.Ioc L U
  let A : ℝ := (((L + 1 : ℕ) : ℝ) * Q) / 2
  let B : ℝ := 2 * (U : ℝ) * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hCast : ((L + 1 : ℕ) : ℝ) ≤ U := by exact_mod_cast hLU
    nlinarith
  have hModeInt : ∀ m ∈ S,
      Integrable (fun r : ℝ =>
        typeIReflectionScaleFactor sigma t m *
          typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    intro m hm
    have hmData := Finset.mem_Ioc.mp hm
    have hmPos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le L) hmData.1)
    exact (integrable_typeICommonMellinMode hsigma (mul_pos hmPos hQ)
      hA hAB).const_mul _
  calc
    (∑ m ∈ Finset.Ioc L U,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      ∑ m ∈ S,
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmData := Finset.mem_Ioc.mp hm
        have hmOne : 1 ≤ m := by omega
        rw [typeIDyadicPhysicalIntegral_rescale
          (by exact_mod_cast (show 0 < m by omega) : (0 : ℝ) < m)
          hQ (by positivity) (by linarith)]
        have hOriginal :
            (∫ v : ℝ,
                typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
              ∫ v in (m : ℝ) * (Q / 2)..(m : ℝ) * (2 * Q),
                typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
          apply integral_typeIDyadicPhysicalIntegrand_eq_interval
            (mul_pos (by exact_mod_cast (show 0 < m by omega)) hQ)
          · exact le_of_eq (by ring)
          · exact le_of_eq (by ring)
        have hNatural :
            (∫ v : ℝ,
                typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
              ∫ v in A..B,
                typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
          apply integral_typeIDyadicPhysicalIntegrand_eq_interval
            (mul_pos (by exact_mod_cast (show 0 < m by omega)) hQ)
          · dsimp only [A]
            have hmLower : L + 1 ≤ m := by omega
            have hmLowerReal : ((L + 1 : ℕ) : ℝ) ≤ m := by
              exact_mod_cast hmLower
            nlinarith
          · dsimp only [B]
            have hmUpperReal : (m : ℝ) ≤ U := by exact_mod_cast hmData.2
            nlinarith
        rw [← hOriginal, hNatural]
        have hFun : typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) =
            fun v : ℝ =>
              (typeIDyadicCutoff (v / ((m : ℝ) * Q)) : ℂ) *
                (gmReflectionPowerWeight sigma v *
                  Complex.exp
                    (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
          funext v
          unfold typeIDyadicPhysicalIntegrand
          congr 3
          ring_nf
        rw [hFun]
        have hmPosReal : (0 : ℝ) < m := by
          exact_mod_cast (show 0 < m by omega)
        have hMellin := typeIDyadicRescaledIntegral_eq_mellinReflection
          (sigma := sigma) (t := t) (q := (m : ℝ) * Q)
          (A := A) (B := B) hsigma (mul_pos hmPosReal hQ) hA hAB
        rw [hMellin]
        unfold typeICommonMellinMode
        simp only [Complex.real_smul]
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∑ m ∈ S,
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        rw [Finset.smul_sum]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ∑ m ∈ S,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        congr 1
        exact (MeasureTheory.integral_finsetSum S hModeInt).symm
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        unfold typeIReflectedIntervalMellinPolynomial
          typeICommonMellinMode
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m hm
        ring

/-- Exact source-normalized Mellin formula for a literal interval of
negative Poisson modes. -/
theorem sourceScalar_mul_negativeInterval_eq_reflectedMellinIntegral
    {sigma t : ℝ} {Q L U : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hLU : L < U) :
    typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedNegativeInterval sigma t Q L U =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [typeINormalizedNegativeInterval, Finset.mul_sum]
  calc
    ∑ m ∈ Finset.Ioc L U,
        typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t
            ((Q : ℝ) * (-(m : ℝ)))) =
      ∑ m ∈ Finset.Ioc L U,
        ∫ x in (Q : ℝ) / 2..2 * (Q : ℝ),
          typeIDyadicPhysicalIntegrand sigma t (m : ℝ) (Q : ℝ) x := by
            apply Finset.sum_congr rfl
            intro m _hm
            exact sourceScalar_mul_normalizedFourier_neg_eq_physicalIntegral
              sigma t (Q : ℝ) m hQr
    _ = _ := sum_typeIDyadicPhysicalIntegral_interval_eq_reflectedMellin
      hsigma hQr hLU

/-- Exact positive-mode companion.  It is obtained by conjugating the
negative formula at the reversed ordinate, preserving cancellation within
the entire interval. -/
theorem sourceScalar_mul_positiveInterval_eq_reflectedMellinIntegral
    {sigma t : ℝ} {Q L U : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hLU : L < U) :
    typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedPositiveInterval sigma t Q L U =
      star ((1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma (-t) (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (-t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q)) := by
  rw [typeINormalizedPositiveInterval, Finset.mul_sum]
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc
    ∑ m ∈ Finset.Ioc L U,
        typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t
            ((Q : ℝ) * (m : ℝ))) =
      ∑ m ∈ Finset.Ioc L U,
        star (∫ x in (Q : ℝ) / 2..2 * (Q : ℝ),
          typeIDyadicPhysicalIntegrand sigma (-t) (m : ℝ) (Q : ℝ) x) := by
            apply Finset.sum_congr rfl
            intro m _hm
            exact sourceScalar_mul_normalizedFourier_pos_eq_conj_physicalIntegral
              sigma t (Q : ℝ) m hQr
    _ = star (∑ m ∈ Finset.Ioc L U,
        ∫ x in (Q : ℝ) / 2..2 * (Q : ℝ),
          typeIDyadicPhysicalIntegrand sigma (-t) (m : ℝ) (Q : ℝ) x) := by
            simp
    _ = _ := congrArg star
      (sum_typeIDyadicPhysicalIntegral_interval_eq_reflectedMellin
        (t := -t) hsigma hQr hLU)

/-- A dyadic interval-form fixed polynomial is exactly an ordinary
Dirichlet polynomial with coefficients normalized at its right endpoint.
This is the source-entry bridge used by MHH after stationary-annulus
pigeonholing. -/
theorem typeIReflectedIntervalFixedPolynomial_dyadic_normalized
    {sigma u : ℝ} {P : ℕ} (hP : 0 < P) :
    typeIReflectedIntervalFixedPolynomial sigma u P (2 * P) /
        ((((2 * P : ℕ) : ℝ) ^ sigma : ℝ) : ℂ) =
      dirichletPoly P (normalizedTypeIReflectedCoeff sigma (2 * P)) (-u) := by
  have hTwoP : 0 < 2 * P := by omega
  have hTwoPReal : (0 : ℝ) < (2 * P : ℕ) := by exact_mod_cast hTwoP
  unfold typeIReflectedIntervalFixedPolynomial dirichletPoly
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have hmData := Finset.mem_Ioc.mp hm
  have hmPos : 0 < m := lt_of_lt_of_le (by omega : 0 < P) hmData.1.le
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hmPos
  rw [normalizedTypeIReflectedCoeff,
    ite_eq_left ⟨hmPos, hmData.2⟩]
  rw [Complex.ofReal_div, Complex.ofReal_cpow hmReal.le,
    Complex.ofReal_cpow hTwoPReal.le]
  have hmComplex : (m : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  rw [Complex.cpow_def_of_ne_zero hmComplex,
    Complex.cpow_def_of_ne_zero hmComplex]
  field_simp
  congr 1
  push_cast
  ring_nf

/-- The coefficients in every normalized reflected dyadic block satisfy
the exact unit bound required by the unrestricted MHH theorem. -/
theorem norm_normalizedTypeIReflectedCoeff_two_mul_le_one
    {sigma : ℝ} (hsigma : 0 ≤ sigma) {P n : ℕ} (hP : 0 < P) :
    ‖normalizedTypeIReflectedCoeff sigma (2 * P) n‖ ≤ 1 :=
  norm_normalizedTypeIReflectedCoeff_le_one hsigma (by omega)

/-- A large fixed interval polynomial gives the corresponding normalized
dyadic Dirichlet polynomial with its exact right-endpoint loss. -/
theorem normalized_reflected_dyadic_large_of_fixed
    {sigma u S : ℝ} {P : ℕ} (hP : 0 < P)
    (hLarge : S <
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 * P)‖) :
    S / ((2 * P : ℕ) : ℝ) ^ sigma <
      ‖dirichletPoly P
        (normalizedTypeIReflectedCoeff sigma (2 * P)) (-u)‖ := by
  have hDen : 0 < ((2 * P : ℕ) : ℝ) ^ sigma := by positivity
  rw [← typeIReflectedIntervalFixedPolynomial_dyadic_normalized hP,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDen]
  exact (div_lt_div_iff_of_pos_right hDen).2 hLarge

/-- Non-strict companion used after finite dyadic pigeonholing. -/
theorem normalized_reflected_dyadic_large_of_fixed_le
    {sigma u S : ℝ} {P : ℕ} (hP : 0 < P)
    (hLarge : S ≤
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 * P)‖) :
    S / ((2 * P : ℕ) : ℝ) ^ sigma ≤
      ‖dirichletPoly P
        (normalizedTypeIReflectedCoeff sigma (2 * P)) (-u)‖ := by
  have hDen : 0 < ((2 * P : ℕ) : ℝ) ^ sigma := by positivity
  rw [← typeIReflectedIntervalFixedPolynomial_dyadic_normalized hP,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDen]
  exact (div_le_div_iff_of_pos_right hDen).2 hLarge

/-- Exact dyadic partition of a reflected interval.  Every block has the
same physical dual scale up to the fixed factor `2^J`; no prefix below the
stationary annulus is introduced. -/
theorem typeIReflectedIntervalFixedPolynomial_eq_sum_dyadic
    (sigma u : ℝ) (P J : ℕ) :
    typeIReflectedIntervalFixedPolynomial sigma u P (2 ^ J * P) =
      ∑ j ∈ Finset.range J,
        typeIReflectedIntervalFixedPolynomial sigma u
          (2 ^ j * P) (2 ^ (j + 1) * P) := by
  induction J with
  | zero => simp [typeIReflectedIntervalFixedPolynomial]
  | succ J ih =>
      rw [Finset.sum_range_succ, ← ih]
      unfold typeIReflectedIntervalFixedPolynomial
      have hPmid : P ≤ 2 ^ J * P :=
        Nat.le_mul_of_pos_left P (pow_pos (by omega : 0 < 2) J)
      have hmidTop : 2 ^ J * P ≤ 2 ^ (J + 1) * P := by
        rw [pow_succ]
        apply Nat.mul_le_mul_right P
        calc
          2 ^ J = 2 ^ J * 1 := by omega
          _ ≤ 2 ^ J * 2 := Nat.mul_le_mul_left _ (by omega)
      rw [← Finset.Ioc_union_Ioc_eq_Ioc hPmid hmidTop,
        Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]

/-- One of the `J` dyadic blocks in a stationary reflected annulus carries
at least the average norm. -/
theorem exists_large_reflected_interval_dyadic_block
    {sigma u R : ℝ} {P J : ℕ} (hJ : 0 < J)
    (hLarge : R ≤
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 ^ J * P)‖) :
    ∃ j ∈ Finset.range J,
      R / J ≤
        ‖typeIReflectedIntervalFixedPolynomial sigma u
          (2 ^ j * P) (2 ^ (j + 1) * P)‖ := by
  have hTriangle :
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 ^ J * P)‖ ≤
        ∑ j ∈ Finset.range J,
          ‖typeIReflectedIntervalFixedPolynomial sigma u
            (2 ^ j * P) (2 ^ (j + 1) * P)‖ := by
    rw [typeIReflectedIntervalFixedPolynomial_eq_sum_dyadic]
    exact norm_sum_le _ _
  exact pigeonhole_real_sum J
    (fun j => ‖typeIReflectedIntervalFixedPolynomial sigma u
      (2 ^ j * P) (2 ^ (j + 1) * P)‖) R
    (hLarge.trans hTriangle) hJ

/-- The preceding stationary-annulus pigeonhole already has the exact
coefficient normalization required by MHH. -/
theorem exists_large_normalized_reflected_interval_dyadic_block
    {sigma u R : ℝ} {P J : ℕ} (hP : 0 < P) (hJ : 0 < J)
    (hLarge : R ≤
      ‖typeIReflectedIntervalFixedPolynomial sigma u P (2 ^ J * P)‖) :
    ∃ j ∈ Finset.range J,
      (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
        ‖dirichletPoly (2 ^ j * P)
          (normalizedTypeIReflectedCoeff sigma (2 ^ (j + 1) * P)) (-u)‖ := by
  obtain ⟨j, hj, hBlock⟩ :=
    exists_large_reflected_interval_dyadic_block hJ hLarge
  have hPj : 0 < 2 ^ j * P := by positivity
  refine ⟨j, hj, ?_⟩
  have hBlock' : R / J ≤
      ‖typeIReflectedIntervalFixedPolynomial sigma u
        (2 ^ j * P) (2 * (2 ^ j * P))‖ := by
    convert hBlock using 2
    rw [pow_succ]
    ring_nf
  have hNorm := normalized_reflected_dyadic_large_of_fixed_le
    (sigma := sigma) (u := u) hPj hBlock'
  simpa only [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_assoc,
    mul_comm, mul_left_comm] using hNorm

/-- Local copy of the multiplicity-preserving displacement selection used
before the later prefix-form reflection lemmas. -/
theorem exists_separated_bounded_shift_image_interval
    (W : Finset ℝ) (shift : ℝ → ℝ) (H : ℝ)
    (_hH : 0 ≤ H) (hSeparated : IsSeparated 1 W)
    (hShift : ∀ t ∈ W, |t - shift t| ≤ H) :
    ∃ U ⊆ W.image shift, IsSeparated 1 U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card := by
  classical
  let weight : ℝ → ℕ := fun _ => 1
  let shiftedWeight : ℝ → ℕ := fun u =>
    ∑ t ∈ W.filter (fun x => shift x = u), weight t
  have hLocalOriginal : ∀ z : ℤ,
      ∑ t ∈ W.filter
          (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1), weight t ≤ 1 := by
    intro z
    have hCard :
        (W.filter (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1)).card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro x y hx hy
      simp only [Finset.mem_filter] at hx hy
      by_contra hxy
      have hSep := hSeparated x hx.1 y hy.1 hxy
      rw [Real.dist_eq] at hSep
      have hlt : |x - y| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
      linarith
    simpa [weight] using hCard
  have hLocalShifted : ∀ z : ℤ,
      ∑ u ∈ (W.image shift).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1), shiftedWeight u ≤
        2 * ⌈H⌉₊ + 1 := by
    intro z
    simpa only [shiftedWeight, weight, mul_one] using
      shifted_bin_weight_le_of_unit_bin_weight W weight id shift H 1
        (by simpa only [id_eq] using hShift) hLocalOriginal z
  obtain ⟨U, hUImage, hUSep, hWeight⟩ :=
    weighted_separated_selection (W.image shift) shiftedWeight
      (2 * ⌈H⌉₊ + 1) hLocalShifted
  have hAll : W.filter (fun t => shift t ∈ W.image shift) = W := by
    apply Finset.filter_eq_self.mpr
    intro t ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter W (W.image shift)
    shift weight
  rw [hAll] at hFiber
  have hTotal : ∑ u ∈ W.image shift, shiftedWeight u = W.card := by
    simpa [shiftedWeight, weight] using hFiber
  refine ⟨U, hUImage, hUSep, ?_⟩
  rw [← hTotal]
  simpa only [mul_assoc] using hWeight

/-- Negative-sign stationary blocks are reflected into one positive base
interval, with all displacement fibres retained. -/
theorem extract_negative_reflected_dyadic_family
    {P : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 * P)‖) :
    ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card ∧
      ∀ v ∈ U,
        S / ((2 * P : ℕ) : ℝ) ^ sigma <
          ‖dirichletPoly P
            (phaseShiftCoeffs (-3 * T)
              (normalizedTypeIReflectedCoeff sigma (2 * P))) v‖ := by
  classical
  let reflect : ℝ → ℝ := fun t => 3 * T - t
  let Wrev : Finset ℝ := W.image reflect
  have hreflectInj : Function.Injective reflect := by
    intro x y hxy
    dsimp only [reflect] at hxy
    linarith
  have hWrevCard : Wrev.card = W.card := by
    dsimp only [Wrev]
    exact Finset.card_image_iff.mpr fun _ hx _ hy hxy =>
      hreflectInj hxy
  have hWrevSeparated : IsSeparated 1 Wrev := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨tx, htx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ty, hty, hyEq⟩
    have htxy : tx ≠ ty := by
      intro h
      subst ty
      exact hxy hyEq
    have hsep := hSeparated tx htx ty hty htxy
    subst y
    rw [Real.dist_eq] at hsep ⊢
    dsimp only [reflect]
    rw [show 3 * T - tx - (3 * T - ty) = -(tx - ty) by ring, abs_neg]
    exact hsep
  have hOriginalMem : ∀ x ∈ Wrev, 3 * T - x ∈ W := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    convert ht using 1
    dsimp only [reflect]
    ring
  let displacement : ℝ → ℝ := fun x =>
    if hx : x ∈ Wrev then Classical.choose (hEach (3 * T - x)
      (hOriginalMem x hx)) else 0
  have hDisplacementMem : ∀ x ∈ Wrev,
      displacement x ∈ Set.Icc (-H) H := by
    intro x hx
    simp only [displacement, dite_eq_left hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).1
  have hDisplacementLarge : ∀ x ∈ Wrev,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma
        ((3 * T - x) + displacement x) P (2 * P)‖ := by
    intro x hx
    simp only [displacement, dite_eq_left hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).2
  let shift : ℝ → ℝ := fun x => x - displacement x
  have hShiftBound : ∀ x ∈ Wrev, |x - shift x| ≤ H := by
    intro x hx
    have hd := hDisplacementMem x hx
    dsimp only [shift]
    rw [show x - (x - displacement x) = displacement x by ring]
    exact abs_le.mpr hd
  obtain ⟨U, hUImage, hUSep, hCard⟩ :=
    exists_separated_bounded_shift_image_interval Wrev shift H hH
      hWrevSeparated hShiftBound
  refine ⟨U, hUSep, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨x, hx, rfl⟩
    have hxRange := hRange (3 * T - x) (hOriginalMem x hx)
    have hdu := hDisplacementMem x hx
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift] <;> linarith [hdu.1, hdu.2]
  · rw [← hWrevCard]
    exact hCard
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨x, hx, rfl⟩
    have hLarge := normalized_reflected_dyadic_large_of_fixed hP
      (hDisplacementLarge x hx)
    have hArg : -((3 * T - x) + displacement x) =
        shift x + (-3 * T) := by
      dsimp only [shift]
      ring
    rw [hArg, dirichletPoly_translate] at hLarge
    exact hLarge

/-- Positive-sign stationary blocks require only the bounded displacement
selection; no reflection of the ordinate is needed. -/
theorem extract_positive_reflected_dyadic_family
    {P : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma (-t + u)
        P (2 * P)‖) :
    ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card ∧
      ∀ v ∈ U,
        S / ((2 * P : ℕ) : ℝ) ^ sigma <
          ‖dirichletPoly P
            (normalizedTypeIReflectedCoeff sigma (2 * P)) v‖ := by
  classical
  let displacement : ℝ → ℝ := fun t =>
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hDisplacementMem : ∀ t ∈ W,
      displacement t ∈ Set.Icc (-H) H := by
    intro t ht
    simp only [displacement, dite_eq_left ht]
    exact (Classical.choose_spec (hEach t ht)).1
  have hDisplacementLarge : ∀ t ∈ W,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma
        (-t + displacement t) P (2 * P)‖ := by
    intro t ht
    simp only [displacement, dite_eq_left ht]
    exact (Classical.choose_spec (hEach t ht)).2
  let shift : ℝ → ℝ := fun t => t - displacement t
  have hShiftBound : ∀ t ∈ W, |t - shift t| ≤ H := by
    intro t ht
    have hd := hDisplacementMem t ht
    dsimp only [shift]
    rw [show t - (t - displacement t) = displacement t by ring]
    exact abs_le.mpr hd
  obtain ⟨U, hUImage, hUSep, hCard⟩ :=
    exists_separated_bounded_shift_image_interval W shift H hH
      hSeparated hShiftBound
  refine ⟨U, hUSep, ?_, hCard, ?_⟩
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨t, ht, rfl⟩
    have htRange := hRange t ht
    have hdu := hDisplacementMem t ht
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift] <;> linarith [hdu.1, hdu.2]
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨t, ht, rfl⟩
    have hLarge := normalized_reflected_dyadic_large_of_fixed hP
      (hDisplacementLarge t ht)
    simpa only [shift, neg_add_rev, neg_neg, sub_eq_add_neg,
      add_comm] using hLarge

/-- MHH cardinality for a negative-sign stationary dyadic block. -/
theorem negative_reflected_dyadic_mhh_cardinality
    {P : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (hDH : D + H ≤ T / 2) (hS : 0 < S)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 * P)‖)
    (hsigma : 0 ≤ sigma) :
    ∃ K : ℝ, 0 < K ∧ ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card ∧
      (U.card : ℝ) ≤
        K * (1 + (((harmonic P : ℚ) : ℝ))) *
          (((P : ℝ) ^ 2 /
              (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 2) +
            (3 * T) * min
              ((P : ℝ) /
                (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 2)
              ((P : ℝ) ^ 4 /
                (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  obtain ⟨U, hUSep, hUBase, hCard, hLarge⟩ :=
    extract_negative_reflected_dyadic_family W hP hH
      (zero_le_one.trans hT) hDH hSeparated hRange hEach
  have hThreshold : 0 < S / ((2 * P : ℕ) : ℝ) ^ sigma := by positivity
  have hCoeff : ∀ n ∈ dyadicInterval P,
      ‖phaseShiftCoeffs (-3 * T)
        (normalizedTypeIReflectedCoeff sigma (2 * P)) n‖ ≤ 1 := by
    intro n _hn
    rw [norm_phaseShiftCoeffs]
    exact norm_normalizedTypeIReflectedCoeff_two_mul_le_one hsigma hP
  have hAt := hMHH P (3 * T)
    (S / ((2 * P : ℕ) : ℝ) ^ sigma) U
    (phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma (2 * P)))
    hP (by linarith) hThreshold hCoeff hUSep hUBase
    (fun v hv => (hLarge v hv).le)
  exact ⟨K, hK, U, hUSep, hUBase, hCard, hAt⟩

/-- MHH cardinality for a positive-sign stationary dyadic block. -/
theorem positive_reflected_dyadic_mhh_cardinality
    {P : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (hDH : D + H ≤ T / 2) (hS : 0 < S)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖typeIReflectedIntervalFixedPolynomial sigma (-t + u)
        P (2 * P)‖)
    (hsigma : 0 ≤ sigma) :
    ∃ K : ℝ, 0 < K ∧ ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card ∧
      (U.card : ℝ) ≤
        K * (1 + (((harmonic P : ℚ) : ℝ))) *
          (((P : ℝ) ^ 2 /
              (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 2) +
            (3 * T) * min
              ((P : ℝ) /
                (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 2)
              ((P : ℝ) ^ 4 /
                (S / ((2 * P : ℕ) : ℝ) ^ sigma) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  obtain ⟨U, hUSep, hUBase, hCard, hLarge⟩ :=
    extract_positive_reflected_dyadic_family W hP hH
      (zero_le_one.trans hT) hDH hSeparated hRange hEach
  have hThreshold : 0 < S / ((2 * P : ℕ) : ℝ) ^ sigma := by positivity
  have hCoeff : ∀ n ∈ dyadicInterval P,
      ‖normalizedTypeIReflectedCoeff sigma (2 * P) n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeIReflectedCoeff_two_mul_le_one hsigma hP
  have hAt := hMHH P (3 * T)
    (S / ((2 * P : ℕ) : ℝ) ^ sigma) U
    (normalizedTypeIReflectedCoeff sigma (2 * P))
    hP (by linarith) hThreshold hCoeff hUSep hUBase
    (fun v hv => (hLarge v hv).le)
  exact ⟨K, hK, U, hUSep, hUBase, hCard, hAt⟩


/-- The common finite reflected Mellin integrand is genuinely Bochner
integrable.  This is the integrand occurring in the exact B-process identity,
not a separately postulated majorant. -/
theorem integrable_typeIReflectedMellinIntegrand
    {sigma t Q : ℝ} {M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    Integrable (fun r : ℝ =>
      typeIReflectedMellinPolynomial sigma t Q M r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            (Q / 2) (2 * M * Q)) := by
  let S := Finset.Icc 1 M
  let A : ℝ := Q / 2
  let B : ℝ := 2 * M * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hMode : ∀ m ∈ S, Integrable (fun r : ℝ =>
      typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    intro m hm
    have hmData := Finset.mem_Icc.mp hm
    have hmPos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmData.1)
    exact (integrable_typeICommonMellinMode hsigma (mul_pos hmPos hQ)
      hA hAB).const_mul _
  have hSum : Integrable (fun r : ℝ =>
      ∑ m ∈ S, typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) :=
    MeasureTheory.integrable_finsetSum S hMode
  apply hSum.congr
  filter_upwards with r
  unfold typeIReflectedMellinPolynomial typeICommonMellinMode
  dsimp only [S, A, B]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- The interval-form reflected Mellin integrand is Bochner integrable. -/
theorem integrable_typeIReflectedIntervalMellinIntegrand
    {sigma t Q : ℝ} {L U : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hLU : L < U) :
    Integrable (fun r : ℝ =>
      typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            ((((L + 1 : ℕ) : ℝ) * Q) / 2)
            (2 * (U : ℝ) * Q)) := by
  let S := Finset.Ioc L U
  let A : ℝ := (((L + 1 : ℕ) : ℝ) * Q) / 2
  let B : ℝ := 2 * (U : ℝ) * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hCast : ((L + 1 : ℕ) : ℝ) ≤ U := by exact_mod_cast hLU
    nlinarith
  have hMode : ∀ m ∈ S, Integrable (fun r : ℝ =>
      typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    intro m hm
    have hmData := Finset.mem_Ioc.mp hm
    have hmPos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le L) hmData.1)
    exact (integrable_typeICommonMellinMode hsigma (mul_pos hmPos hQ)
      hA hAB).const_mul _
  have hSum : Integrable (fun r : ℝ =>
      ∑ m ∈ S, typeIReflectionScaleFactor sigma t m *
        typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) :=
    MeasureTheory.integrable_finsetSum S hMode
  apply hSum.congr
  filter_upwards with r
  unfold typeIReflectedIntervalMellinPolynomial typeICommonMellinMode
  dsimp only [S, A, B]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- Elementary uniform bound for a literal reflected interval. -/
theorem norm_typeIReflectedIntervalFixedPolynomial_le
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u : ℝ) (L U : ℕ) :
    ‖typeIReflectedIntervalFixedPolynomial sigma u L U‖ ≤
      (U : ℝ) * (U : ℝ) ^ sigma := by
  rw [typeIReflectedIntervalFixedPolynomial]
  calc
    ‖∑ m ∈ Finset.Ioc L U,
        (((m : ℝ) ^ sigma : ℝ) : ℂ) *
          (m : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
      ∑ m ∈ Finset.Ioc L U,
        ‖(((m : ℝ) ^ sigma : ℝ) : ℂ) *
          (m : ℂ) ^ ((u : ℂ) * Complex.I)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Ioc L U, (U : ℝ) ^ sigma := by
      apply Finset.sum_le_sum
      intro m hm
      have hmData := Finset.mem_Ioc.mp hm
      have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le L) hmData.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
        Complex.norm_natCast_cpow_of_pos hmPos]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, Real.rpow_zero,
        mul_one]
      exact Real.rpow_le_rpow (Nat.cast_nonneg m)
        (by exact_mod_cast hmData.2) hsigma
    _ ≤ (U : ℝ) * (U : ℝ) ^ sigma := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hCard : (Finset.Ioc L U).card ≤ U := by simp
      gcongr

/-- The fixed interval polynomial is the only non-unit factor in its
Mellin polynomial. -/
theorem norm_typeIReflectedIntervalMellinPolynomial_eq_fixed
    (sigma t Q : ℝ) (L U : ℕ) (r : ℝ) (hQ : 0 < Q) :
    ‖typeIReflectedIntervalMellinPolynomial sigma t Q L U r‖ =
      Q * ‖typeIReflectedIntervalFixedPolynomial sigma (t + r) L U‖ := by
  rw [typeIReflectedIntervalMellinPolynomial_eq_fixed sigma t Q L U r hQ,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

/-- Setwise norm bound for the exact interval-form Mellin integral. -/
theorem norm_setIntegral_typeIReflectedIntervalMellinIntegrand_le
    {sigma t Q R K : ℝ} {L U : ℕ} {S : Set ℝ}
    (hS : MeasurableSet S) (hQ : 0 < Q) (hR : 0 ≤ R)
    (hFixed : ∀ r ∈ S,
      ‖typeIReflectedIntervalFixedPolynomial sigma (t + r) L U‖ ≤ R)
    (hKernel : ∀ r ∈ S,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        ((((L + 1 : ℕ) : ℝ) * Q) / 2)
        (2 * (U : ℝ) * Q)‖ ≤ K) :
    ‖∫ r : ℝ in S,
        typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              ((((L + 1 : ℕ) : ℝ) * Q) / 2)
              (2 * (U : ℝ) * Q)‖ ≤
      Q * R * K * ∫ r : ℝ in S, ‖typeIDyadicCutoffMellin r‖ := by
  have hMellin : Integrable typeIDyadicCutoffMellin := by
    unfold typeIDyadicCutoffMellin
    simpa only [VerticalIntegrable, Complex.ofReal_one] using
      verticalIntegrable_typeIDyadicCutoffMellin
  have hDom : IntegrableOn
      (fun r : ℝ => Q * R * K * ‖typeIDyadicCutoffMellin r‖) S :=
    hMellin.norm.const_mul (Q * R * K) |>.integrableOn
  have hPoint : ∀ᵐ r : ℝ ∂volume.restrict S,
      ‖typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              ((((L + 1 : ℕ) : ℝ) * Q) / 2)
              (2 * (U : ℝ) * Q)‖ ≤
        Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by
    filter_upwards [ae_restrict_mem hS] with r hr
    rw [norm_mul, norm_mul,
      norm_typeIReflectedIntervalMellinPolynomial_eq_fixed
        sigma t Q L U r hQ]
    have hF := hFixed r hr
    have hP := hKernel r hr
    calc
      Q * ‖typeIReflectedIntervalFixedPolynomial sigma (t + r) L U‖ *
          ‖typeIDyadicCutoffMellin r‖ *
            ‖typeIPowerReflectionIntegral sigma (t + r)
              ((((L + 1 : ℕ) : ℝ) * Q) / 2)
              (2 * (U : ℝ) * Q)‖ ≤
        Q * R * ‖typeIDyadicCutoffMellin r‖ * K := by gcongr
      _ = Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by ring
  simpa only [integral_const_mul] using
    norm_integral_le_of_norm_le hDom hPoint

/-- A setwise norm bound for the exact reflected Mellin integral.  The
coefficient polynomial and the oscillatory kernel are bounded separately,
while the literal Mellin transform retains its full `L¹` mass. -/
theorem norm_setIntegral_typeIReflectedMellinIntegrand_le
    {sigma t Q R K : ℝ} {M : ℕ} {S : Set ℝ}
    (hS : MeasurableSet S) (hQ : 0 < Q) (hR : 0 ≤ R)
    (hFixed : ∀ r ∈ S,
      ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ ≤ R)
    (hKernel : ∀ r ∈ S,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤ K) :
    ‖∫ r : ℝ in S,
        typeIReflectedMellinPolynomial sigma t Q M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              (Q / 2) (2 * M * Q)‖ ≤
      Q * R * K * ∫ r : ℝ in S, ‖typeIDyadicCutoffMellin r‖ := by
  have hMellin : Integrable typeIDyadicCutoffMellin := by
    unfold typeIDyadicCutoffMellin
    simpa only [VerticalIntegrable, Complex.ofReal_one] using
      verticalIntegrable_typeIDyadicCutoffMellin
  have hDom : IntegrableOn
      (fun r : ℝ => Q * R * K * ‖typeIDyadicCutoffMellin r‖) S :=
    hMellin.norm.const_mul (Q * R * K) |>.integrableOn
  have hPoint : ∀ᵐ r : ℝ ∂volume.restrict S,
      ‖typeIReflectedMellinPolynomial sigma t Q M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              (Q / 2) (2 * M * Q)‖ ≤
        Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by
    filter_upwards [ae_restrict_mem hS] with r hr
    rw [norm_mul, norm_mul,
      norm_typeIReflectedMellinPolynomial_eq_fixed sigma t Q M r hQ]
    have hF := hFixed r hr
    have hP := hKernel r hr
    calc
      Q * ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ *
          ‖typeIDyadicCutoffMellin r‖ *
            ‖typeIPowerReflectionIntegral sigma (t + r)
              (Q / 2) (2 * M * Q)‖ ≤
        Q * R * ‖typeIDyadicCutoffMellin r‖ * K := by gcongr
      _ = Q * R * K * ‖typeIDyadicCutoffMellin r‖ := by ring
  simpa only [integral_const_mul] using
    norm_integral_le_of_norm_le hDom hPoint

/-! The remaining lemmas specialize the preceding exact estimate to the
bounded Mellin window and its complement. -/

/-- Uniform stationary-window upper bound on the common oscillatory
integral.  Only the proved first/second derivative estimate is used. -/
theorem norm_typeIPowerReflectionIntegral_le_on_symmetric_window
    {sigma t H Q : ℝ} {M : ℕ}
    (hsigma : 0 < sigma) (ht : 2 ≤ t)
    (hHt : 2 * H ≤ t - 2) (hQ : 0 < Q) (hM : 1 ≤ M)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤
      (16 / t) * (Q / 2) ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          (t / 2) ^ (-sigma - 1 / 2) := by
  have htPos : 0 < t := by linarith
  have hTau : 1 ≤ t + r := by
    have hrLower := hr.1
    linarith
  have hA : 0 < Q / 2 := by positivity
  have hAB : Q / 2 ≤ 2 * M * Q := by
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hRaw := norm_typeIPowerReflectionIntegral_le_stationary
    hsigma hTau hA hAB
  have hTauLower : t / 2 ≤ t + r := by
    have hrLower := hr.1
    linarith
  have hTauPos : 0 < t + r := zero_lt_one.trans_le hTau
  have hHalfPos : 0 < t / 2 := by positivity
  have hInv : 8 / (t + r) ≤ 16 / t := by
    rw [div_le_div_iff₀ hTauPos htPos]
    nlinarith
  have hExp : -sigma - 1 / 2 ≤ 0 := by linarith
  have hPow : (t + r) ^ (-sigma - 1 / 2) ≤
      (t / 2) ^ (-sigma - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos hHalfPos hTauLower hExp
  calc
    ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤
      (8 / (t + r)) * (Q / 2) ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          (t + r) ^ (-sigma - 1 / 2) := hRaw
    _ ≤ (16 / t) * (Q / 2) ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          (t / 2) ^ (-sigma - 1 / 2) := by gcongr

/-- The complementary Mellin range is polynomially small to arbitrary
order, with every finite `M` and `Q` dependence displayed. -/
theorem exists_norm_typeIReflectedMellinIntegral_tail_le
    (n : ℕ) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {sigma t Q H : ℝ} {M : ℕ},
      0 ≤ sigma → 0 < Q → 1 ≤ M → 1 ≤ H →
      ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * ((M : ℝ) * (M : ℝ) ^ sigma) *
          (((2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2))) *
            C * H ^ (1 - (n : ℝ))) := by
  obtain ⟨C, hC, hTail⟩ := exists_typeIDyadicCutoffMellin_tail_bound n hn
  refine ⟨C, hC, ?_⟩
  intro sigma t Q H M hsigma hQ hM hH
  have hA : 0 < Q / 2 := by positivity
  have hAB : Q / 2 ≤ 2 * M * Q := by
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hBase := norm_setIntegral_typeIReflectedMellinIntegrand_le
    measurableSet_Icc.compl hQ
    (mul_nonneg (Nat.cast_nonneg M) (Real.rpow_nonneg (Nat.cast_nonneg M) _))
    (S := (Set.Icc (-H) H)ᶜ)
    (R := (M : ℝ) * (M : ℝ) ^ sigma)
    (K := (2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2)))
    (fun r _hr => norm_typeIReflectedFixedPolynomial_le hsigma (t + r) M)
    (fun r _hr => norm_typeIPowerReflectionIntegral_le_trivial
      hsigma hA hAB)
  calc
    ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2))) *
            ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
              ‖typeIDyadicCutoffMellin r‖ := hBase
    _ ≤ Q * ((M : ℝ) * (M : ℝ) ^ sigma) *
          (((2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2))) *
            C * H ^ (1 - (n : ℝ))) := by
      have hFront : 0 ≤ Q * ((M : ℝ) * (M : ℝ) ^ sigma) := by
        positivity
      have hKernel : 0 ≤
          (2 * M * Q - Q / 2) * ((Q / 2) ^ (-sigma) / (Q / 2)) := by
        have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
        positivity
      have hMul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hTail H hH) hKernel) hFront
      simpa only [mul_assoc] using hMul

/-- Complementary Mellin decay for a literal interval of reflected modes.
Unlike the prefix estimate above, this retains both endpoints of the
stationary annulus and is therefore suitable for the exact three-way Poisson
split. -/
theorem exists_norm_typeIReflectedIntervalMellinIntegral_tail_le
    (n : ℕ) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {sigma t Q H : ℝ} {L U : ℕ},
      0 ≤ sigma → 0 < Q → L < U → 1 ≤ H →
      ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q)‖ ≤
        Q * ((U : ℝ) * (U : ℝ) ^ sigma) *
          (((2 * (U : ℝ) * Q - ((((L + 1 : ℕ) : ℝ) * Q) / 2)) *
              ((((((L + 1 : ℕ) : ℝ) * Q) / 2) ^ (-sigma)) /
                ((((L + 1 : ℕ) : ℝ) * Q) / 2))) *
            C * H ^ (1 - (n : ℝ))) := by
  obtain ⟨C, hC, hTail⟩ := exists_typeIDyadicCutoffMellin_tail_bound n hn
  refine ⟨C, hC, ?_⟩
  intro sigma t Q H L U hsigma hQ hLU hH
  let A : ℝ := (((L + 1 : ℕ) : ℝ) * Q) / 2
  let B : ℝ := 2 * (U : ℝ) * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hCast : ((L + 1 : ℕ) : ℝ) ≤ U := by exact_mod_cast hLU
    nlinarith
  have hR : 0 ≤ (U : ℝ) * (U : ℝ) ^ sigma := by positivity
  have hBase := norm_setIntegral_typeIReflectedIntervalMellinIntegrand_le
    measurableSet_Icc.compl hQ hR
    (S := (Set.Icc (-H) H)ᶜ)
    (R := (U : ℝ) * (U : ℝ) ^ sigma)
    (K := (B - A) * (A ^ (-sigma) / A))
    (fun r _hr => norm_typeIReflectedIntervalFixedPolynomial_le
      hsigma (t + r) L U)
    (fun r _hr => norm_typeIPowerReflectionIntegral_le_trivial
      hsigma hA hAB)
  calc
    ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B‖ ≤
        Q * ((U : ℝ) * (U : ℝ) ^ sigma) *
          ((B - A) * (A ^ (-sigma) / A)) *
            ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
              ‖typeIDyadicCutoffMellin r‖ := hBase
    _ ≤ Q * ((U : ℝ) * (U : ℝ) ^ sigma) *
          (((B - A) * (A ^ (-sigma) / A)) *
            C * H ^ (1 - (n : ℝ))) := by
      have hFront : 0 ≤ Q * ((U : ℝ) * (U : ℝ) ^ sigma) := by positivity
      have hKernel : 0 ≤ (B - A) * (A ^ (-sigma) / A) := by positivity
      have hMul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hTail H hH) hKernel) hFront
      simpa only [mul_assoc] using hMul
    _ = Q * ((U : ℝ) * (U : ℝ) ^ sigma) *
          (((2 * (U : ℝ) * Q - ((((L + 1 : ℕ) : ℝ) * Q) / 2)) *
              ((((((L + 1 : ℕ) : ℝ) * Q) / 2) ^ (-sigma)) /
                ((((L + 1 : ℕ) : ℝ) * Q) / 2))) *
            C * H ^ (1 - (n : ℝ))) := by rfl

/-- A uniform nonstationary estimate when the entire physical interval lies
to the left of every stationary point on the symmetric Mellin window. -/
theorem norm_typeIPowerReflectionIntegral_le_left_on_symmetric_window
    {sigma t H A B : ℝ} (hsigma : 0 < sigma) (hA : 0 < A)
    (hAB : A ≤ B) (hleft : 2 * Real.pi * B + H < t)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (t + r) A B‖ ≤
      (4 / (t - H - 2 * Real.pi * B)) * A ^ (-sigma) := by
  have hphase : 2 * Real.pi * B < t + r := by
    have hrLower := hr.1
    linarith
  have hRaw := norm_powerWeighted_gmReflectionIntegral_le_left
    hsigma hA hAB hphase
  have hDen : 0 < t - H - 2 * Real.pi * B := by linarith
  have hDen' : t - H - 2 * Real.pi * B ≤
      t + r - 2 * Real.pi * B := by linarith [hr.1]
  have hFrac : 4 / (t + r - 2 * Real.pi * B) ≤
      4 / (t - H - 2 * Real.pi * B) := by
    exact div_le_div_of_nonneg_left (by norm_num) hDen
      hDen'
  exact hRaw.trans (mul_le_mul_of_nonneg_right hFrac
    (Real.rpow_nonneg hA.le _))

/-- A uniform nonstationary estimate when the entire physical interval lies
to the right of every stationary point on the symmetric Mellin window. -/
theorem norm_typeIPowerReflectionIntegral_le_right_on_symmetric_window
    {sigma t H A B : ℝ} (hsigma : 0 < sigma) (hA : 0 < A)
    (hAB : A ≤ B) (hright : t + H < 2 * Real.pi * A)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (t + r) A B‖ ≤
      (4 / (2 * Real.pi * A - (t + H))) * A ^ (-sigma) := by
  have hphase : t + r < 2 * Real.pi * A := by
    have hrUpper := hr.2
    linarith
  have hRaw := norm_powerWeighted_gmReflectionIntegral_le_right
    hsigma hA hAB hphase
  have hDen : 0 < 2 * Real.pi * A - (t + H) := by linarith
  have hDen' : 2 * Real.pi * A - (t + H) ≤
      2 * Real.pi * A - (t + r) := by linarith [hr.2]
  have hFrac : 4 / (2 * Real.pi * A - (t + r)) ≤
      4 / (2 * Real.pi * A - (t + H)) := by
    exact div_le_div_of_nonneg_left (by norm_num) hDen
      hDen'
  exact hRaw.trans (mul_le_mul_of_nonneg_right hFrac
    (Real.rpow_nonneg hA.le _))

/-- On the same symmetric Mellin window the reversed-ordinate integral is
uniformly nonstationary. -/
theorem norm_typeIPowerReflectionIntegral_neg_le_on_symmetric_window
    {sigma t H Q : ℝ} {M : ℕ}
    (hsigma : 0 < sigma) (ht : 0 < t) (hHt : 2 * H ≤ t)
    (hQ : 0 < Q) (hM : 1 ≤ M)
    {r : ℝ} (hr : r ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (-t + r)
        (Q / 2) (2 * M * Q)‖ ≤
      (8 / t) * (Q / 2) ^ (-sigma) := by
  have hA : 0 < Q / 2 := by positivity
  have hAB : Q / 2 ≤ 2 * M * Q := by
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hRight : -t + r < 2 * Real.pi * (Q / 2) := by
    have hrUpper := hr.2
    have hNeg : -t + r ≤ -t / 2 := by linarith
    have hPiQ : 0 < 2 * Real.pi * (Q / 2) := by positivity
    linarith
  have hRaw := norm_powerWeighted_gmReflectionIntegral_le_right
    hsigma hA hAB hRight
  have hDen : t / 2 ≤ 2 * Real.pi * (Q / 2) - (-t + r) := by
    have hrUpper := hr.2
    have hPiQ : 0 ≤ 2 * Real.pi * (Q / 2) := by positivity
    linarith
  have hDenPos : 0 < 2 * Real.pi * (Q / 2) - (-t + r) := by
    linarith
  have hFrac : 4 / (2 * Real.pi * (Q / 2) - (-t + r)) ≤ 8 / t := by
    rw [div_le_div_iff₀ hDenPos ht]
    nlinarith
  exact hRaw.trans (mul_le_mul_of_nonneg_right hFrac
    (Real.rpow_nonneg hA.le _))

/-- Literal `L¹` mass of the fixed dyadic Mellin kernel. -/
noncomputable def typeIDyadicCutoffMellinL1 : ℝ :=
  ∫ r : ℝ, ‖typeIDyadicCutoffMellin r‖

theorem typeIDyadicCutoffMellinL1_nonneg :
    0 ≤ typeIDyadicCutoffMellinL1 := by
  unfold typeIDyadicCutoffMellinL1
  exact integral_nonneg fun _ => norm_nonneg _

/-- Restricting the fixed Mellin kernel cannot increase its total `L¹`
mass. -/
theorem integral_norm_typeIDyadicCutoffMellin_restrict_le
    (S : Set ℝ) :
    ∫ r : ℝ in S, ‖typeIDyadicCutoffMellin r‖ ≤
      typeIDyadicCutoffMellinL1 := by
  have hInt : Integrable (fun r : ℝ => ‖typeIDyadicCutoffMellin r‖) := by
    have hMellin : Integrable typeIDyadicCutoffMellin := by
      unfold typeIDyadicCutoffMellin
      simpa only [VerticalIntegrable, Complex.ofReal_one] using
        verticalIntegrable_typeIDyadicCutoffMellin
    exact hMellin.norm
  unfold typeIDyadicCutoffMellinL1
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall fun _ => norm_nonneg _) hInt

/-- Exact norm assembly for one interval of negative Poisson modes.  It is
the reusable bridge from a uniform central-kernel estimate and a genuine
Mellin-tail estimate back to the source-normalized finite interval. -/
theorem norm_sourceScalar_mul_negativeInterval_le_of_kernel_tail
    {sigma t H K E : ℝ} {Q L U : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hLU : L < U)
    (_hH : 0 ≤ H) (_hK : 0 ≤ K)
    (hKernel : ∀ r ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        ((((L + 1 : ℕ) : ℝ) * (Q : ℝ)) / 2)
        (2 * (U : ℝ) * (Q : ℝ))‖ ≤ K)
    (hTail :
      ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          typeIReflectedIntervalMellinPolynomial sigma t (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * (Q : ℝ)) / 2)
                (2 * (U : ℝ) * (Q : ℝ))‖ ≤ E) :
    ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedNegativeInterval sigma t Q L U‖ ≤
      (1 / (2 * Real.pi)) *
        ((Q : ℝ) * ((U : ℝ) * (U : ℝ) ^ sigma) * K *
          typeIDyadicCutoffMellinL1 + E) := by
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hR : 0 ≤ (U : ℝ) * (U : ℝ) ^ sigma := by positivity
  have hCentral := norm_setIntegral_typeIReflectedIntervalMellinIntegrand_le
    measurableSet_Icc hQReal hR
    (S := Set.Icc (-H) H)
    (R := (U : ℝ) * (U : ℝ) ^ sigma) (K := K)
    (fun r _hr => norm_typeIReflectedIntervalFixedPolynomial_le
      hsigma (t + r) L U) hKernel
  have hMass := integral_norm_typeIDyadicCutoffMellin_restrict_le
    (Set.Icc (-H) H)
  have hCentral' :
      ‖∫ r : ℝ in Set.Icc (-H) H,
          typeIReflectedIntervalMellinPolynomial sigma t (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * (Q : ℝ)) / 2)
                (2 * (U : ℝ) * (Q : ℝ))‖ ≤
        (Q : ℝ) * ((U : ℝ) * (U : ℝ) ^ sigma) * K *
          typeIDyadicCutoffMellinL1 := by
    exact hCentral.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have hInt := integrable_typeIReflectedIntervalMellinIntegrand
    (sigma := sigma) (t := t) (Q := (Q : ℝ)) hsigma hQReal hLU
  have hSplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hInt
  have hWhole :
      ‖∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t (Q : ℝ) L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * (Q : ℝ)) / 2)
                (2 * (U : ℝ) * (Q : ℝ))‖ ≤
        (Q : ℝ) * ((U : ℝ) * (U : ℝ) ^ sigma) * K *
          typeIDyadicCutoffMellinL1 + E := by
    rw [← hSplit]
    exact (norm_add_le _ _).trans (add_le_add hCentral' hTail)
  have hEq := sourceScalar_mul_negativeInterval_eq_reflectedMellinIntegral
    (t := t) hsigma hQ hLU
  have hNorm := congrArg norm hEq
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] at hNorm
  rw [hNorm]
  exact mul_le_mul_of_nonneg_left hWhole (by positivity)

/-- A large exact interval-form Mellin integral forces a large fixed
interval polynomial at one bounded ordinate displacement. -/
theorem exists_large_typeIReflectedIntervalFixedPolynomial_of_integral
    {sigma t Q H X R K E : ℝ} {L U : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hLU : L < U)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hKernel : ∀ r ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        ((((L + 1 : ℕ) : ℝ) * Q) / 2)
        (2 * (U : ℝ) * Q)‖ ≤ K)
    (hLarge : X ≤ ‖∫ r : ℝ,
      typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            ((((L + 1 : ℕ) : ℝ) * Q) / 2)
            (2 * (U : ℝ) * Q)‖)
    (hTail : ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
      typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            ((((L + 1 : ℕ) : ℝ) * Q) / 2)
            (2 * (U : ℝ) * Q)‖ ≤ E)
    (hGap : Q * R * K * typeIDyadicCutoffMellinL1 + E < X) :
    ∃ r ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedIntervalFixedPolynomial sigma (t + r) L U‖ := by
  by_contra h
  push Not at h
  have hK : 0 ≤ K := by
    have hZeroMem : (0 : ℝ) ∈ Set.Icc (-H) H := by
      constructor <;> linarith
    exact (norm_nonneg _).trans (hKernel 0 hZeroMem)
  have hCentral := norm_setIntegral_typeIReflectedIntervalMellinIntegrand_le
    measurableSet_Icc hQ hR
    (S := Set.Icc (-H) H) (R := R) (K := K) h hKernel
  have hMass := integral_norm_typeIDyadicCutoffMellin_restrict_le
    (Set.Icc (-H) H)
  have hCentral' :
      ‖∫ r : ℝ in Set.Icc (-H) H,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 := by
    exact hCentral.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have hInt := integrable_typeIReflectedIntervalMellinIntegrand
    (t := t) hsigma hQ hLU
  have hSplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hInt
  have hWhole :
      ‖∫ r : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t Q L U r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((((L + 1 : ℕ) : ℝ) * Q) / 2)
                (2 * (U : ℝ) * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 + E := by
    rw [← hSplit]
    exact (norm_add_le _ _).trans (add_le_add hCentral' hTail)
  linarith

/-- A large exact reflected Mellin integral forces a large value of the
fixed reflected polynomial at one bounded ordinate displacement.  The tail
and central-kernel losses are explicit premises, not hidden in a choice. -/
theorem exists_large_typeIReflectedFixedPolynomial_of_integral
    {sigma t Q H L R K E : ℝ} {M : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hKernel : ∀ r ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + r)
        (Q / 2) (2 * M * Q)‖ ≤ K)
    (hLarge : L ≤ ‖∫ r : ℝ,
      typeIReflectedMellinPolynomial sigma t Q M r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            (Q / 2) (2 * M * Q)‖)
    (hTail : ‖∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
      typeIReflectedMellinPolynomial sigma t Q M r *
        typeIDyadicCutoffMellin r *
          typeIPowerReflectionIntegral sigma (t + r)
            (Q / 2) (2 * M * Q)‖ ≤ E)
    (hGap : Q * R * K * typeIDyadicCutoffMellinL1 + E < L) :
    ∃ r ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ := by
  by_contra h
  push Not at h
  have hK : 0 ≤ K := by
    have hZeroMem : (0 : ℝ) ∈ Set.Icc (-H) H := by
      constructor <;> linarith
    exact (norm_nonneg _).trans (hKernel 0 hZeroMem)
  have hCentral := norm_setIntegral_typeIReflectedMellinIntegrand_le
    measurableSet_Icc hQ hR
    (S := Set.Icc (-H) H) (R := R) (K := K) h hKernel
  have hMass := integral_norm_typeIDyadicCutoffMellin_restrict_le
    (Set.Icc (-H) H)
  have hCentral' :
      ‖∫ r : ℝ in Set.Icc (-H) H,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 := by
    exact hCentral.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have hInt := integrable_typeIReflectedMellinIntegrand
    (t := t) hsigma hQ hM
  have hSplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hInt
  have hWhole :
      ‖∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q)‖ ≤
        Q * R * K * typeIDyadicCutoffMellinL1 + E := by
    rw [← hSplit]
    exact (norm_add_le _ _).trans (add_le_add hCentral' hTail)
  linarith

/-- Norm form of the exact negative-mode Mellin identity. -/
theorem norm_typeIReflectedMellinIntegral_eq_two_pi_mul_negativeModes
    {sigma t : ℝ} {Q M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    ‖∫ r : ℝ,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖ =
      2 * Real.pi *
        ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedNegativeModes sigma t Q M‖ := by
  have hEq := sourceScalar_mul_negativeModes_eq_reflectedMellinIntegral
    (t := t) hsigma hQ hM
  have hNorm := congrArg norm hEq
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity :
      0 < 1 / (2 * Real.pi))] at hNorm
  have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hNorm]
  field_simp

/-- Norm form of the exact positive-mode Mellin identity.  Conjugation
changes neither side's norm, so the same `2π` normalization as in the
negative half is retained. -/
theorem norm_typeIReflectedPositiveMellinIntegral_eq_two_pi_mul_positiveModes
    {sigma t : ℝ} {Q M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    ‖∫ r : ℝ,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (-t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖ =
      2 * Real.pi *
        ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedPositiveModes sigma t Q M‖ := by
  have hEq := sourceScalar_mul_positiveModes_eq_reflectedMellinIntegral
    (t := t) hsigma hQ hM
  have hNorm := congrArg norm hEq
  simp only [norm_star, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] at hNorm
  rw [hNorm]
  field_simp [Real.pi_ne_zero]

/-- A large retained negative half forces a large value of the common
fixed reflected polynomial at a bounded Mellin displacement. -/
theorem exists_large_reflectedFixedPolynomial_of_negativeModes
    {sigma t H L R K E : ℝ} {Q M : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : L ≤
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedNegativeModes sigma t Q M‖)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ E)
    (hGap : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
      2 * Real.pi * L) :
    ∃ u ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedFixedPolynomial sigma (t + u) M‖ := by
  have hIntegralEq := norm_typeIReflectedMellinIntegral_eq_two_pi_mul_negativeModes
    (sigma := sigma) (t := t) (Q := Q) (M := M) hsigma hQ hM
  have hIntegralLarge : 2 * Real.pi * L ≤
      ‖∫ u : ℝ,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ := by
    rw [hIntegralEq]
    exact mul_le_mul_of_nonneg_left hLarge (by positivity)
  exact exists_large_typeIReflectedFixedPolynomial_of_integral
    hsigma (by exact_mod_cast hQ) hM hH hR hKernel hIntegralLarge hTail hGap

/-- The corresponding extraction for the retained positive half.  Its
fixed polynomial occurs at the reversed source ordinate, exactly as in the
proved conjugation identity. -/
theorem exists_large_reflectedFixedPolynomial_of_positiveModes
    {sigma t H L R K E : ℝ} {Q M : ℕ}
    (hsigma : 0 ≤ sigma) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : L ≤
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedPositiveModes sigma t Q M‖)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (-t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (-t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ E)
    (hGap : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
      2 * Real.pi * L) :
    ∃ u ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedFixedPolynomial sigma (-t + u) M‖ := by
  have hIntegralEq :=
    norm_typeIReflectedPositiveMellinIntegral_eq_two_pi_mul_positiveModes
      (sigma := sigma) (t := t) (Q := Q) (M := M) hsigma hQ hM
  have hIntegralLarge : 2 * Real.pi * L ≤
      ‖∫ u : ℝ,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (-t + u)
              ((Q : ℝ) / 2) (2 * M * Q)‖ := by
    rw [hIntegralEq]
    exact mul_le_mul_of_nonneg_left hLarge (by positivity)
  exact exists_large_typeIReflectedFixedPolynomial_of_integral
    hsigma (by exact_mod_cast hQ) hM hH hR hKernel hIntegralLarge hTail hGap

/-- The complete positive-mode block is nonstationary on the bounded
Mellin window; outside that window the arbitrary-order Mellin tail applies.
Every dependence on the dual cutoff is explicit. -/
theorem exists_norm_sourceScalar_mul_positiveModes_le
    (n : ℕ) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {sigma t H : ℝ} {Q M : ℕ},
      0 < sigma → 0 < t → 1 ≤ H → 2 * H ≤ t →
      0 < Q → 1 ≤ M →
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedPositiveModes sigma t Q M‖ ≤
        (1 / (2 * Real.pi)) *
          ((Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
              ((8 / t) * ((Q : ℝ) / 2) ^ (-sigma)) *
                typeIDyadicCutoffMellinL1 +
            (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
              ((2 * (M : ℝ) * (Q : ℝ) - (Q : ℝ) / 2) *
                  (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2)) *
                C * H ^ (1 - (n : ℝ)))) := by
  obtain ⟨C, hC, hTail⟩ := exists_norm_typeIReflectedMellinIntegral_tail_le n hn
  refine ⟨C, hC, ?_⟩
  intro sigma t H Q M hsigma ht hH hHt hQ hM
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hR : 0 ≤ (M : ℝ) * (M : ℝ) ^ sigma := by positivity
  have hCentral := norm_setIntegral_typeIReflectedMellinIntegrand_le
    measurableSet_Icc hQReal hR
    (S := Set.Icc (-H) H)
    (t := -t) (R := (M : ℝ) * (M : ℝ) ^ sigma)
    (K := (8 / t) * ((Q : ℝ) / 2) ^ (-sigma))
    (fun r _hr => norm_typeIReflectedFixedPolynomial_le hsigma.le (-t + r) M)
    (fun r hr => norm_typeIPowerReflectionIntegral_neg_le_on_symmetric_window
      hsigma ht hHt hQReal hM hr)
  have hMass := integral_norm_typeIDyadicCutoffMellin_restrict_le
    (Set.Icc (-H) H)
  have hCentral' :
      ‖∫ r : ℝ in Set.Icc (-H) H,
          typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (-t + r)
                ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
        (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((8 / t) * ((Q : ℝ) / 2) ^ (-sigma)) *
            typeIDyadicCutoffMellinL1 := by
    exact hCentral.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have hTail' := hTail (sigma := sigma) (t := -t) (Q := (Q : ℝ))
    (H := H) (M := M) hsigma.le hQReal hM hH
  have hInt := integrable_typeIReflectedMellinIntegrand
    (sigma := sigma) (t := -t) (Q := (Q : ℝ)) hsigma.le hQReal hM
  have hSplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hInt
  have hWhole :
      ‖∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (-t + r)
                ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
        (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
              ((8 / t) * ((Q : ℝ) / 2) ^ (-sigma)) *
                typeIDyadicCutoffMellinL1 +
            (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
              ((2 * (M : ℝ) * (Q : ℝ) - (Q : ℝ) / 2) *
                  (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2)) *
                C * H ^ (1 - (n : ℝ))) := by
    rw [← hSplit]
    exact (norm_add_le _ _).trans (add_le_add hCentral' hTail')
  have hEq := sourceScalar_mul_positiveModes_eq_reflectedMellinIntegral
    (t := t) hsigma.le hQ hM
  have hNorm := congrArg norm hEq
  simp only [norm_star, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] at hNorm
  rw [hNorm]
  exact mul_le_mul_of_nonneg_left hWhole (by positivity)

/-- Zero-mode decay after restoring the exact source normalization. -/
theorem exists_sourceScalar_zeroMode_decay (sigma : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (Q : ℕ), 0 < Q →
      |t| ^ j *
        ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ ≤
        (Q : ℝ) ^ (1 - sigma) * C := by
  obtain ⟨C, hC, hDecay⟩ := typeINormalizedFourier_zero_uniform_decay sigma j
  refine ⟨C, hC, ?_⟩
  intro t Q hQ
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hNormQ : ‖(Q : ℂ)‖ = (Q : ℝ) := by
    rw [Complex.norm_natCast]
  have hQP : (Q : ℝ) ^ (-sigma) * (Q : ℝ) =
      (Q : ℝ) ^ (1 - sigma) := by
    calc
      (Q : ℝ) ^ (-sigma) * (Q : ℝ) =
          (Q : ℝ) ^ (-sigma) * (Q : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (Q : ℝ) ^ (-sigma + 1) := by
            rw [Real.rpow_add hQReal]
      _ = (Q : ℝ) ^ (1 - sigma) := by ring_nf
  rw [norm_mul, norm_mul,
    norm_typeISourceNormalizationScalar sigma t (Q : ℝ) hQReal,
    hNormQ]
  calc
    |t| ^ j * ((Q : ℝ) ^ (-sigma) *
          ((Q : ℝ) * ‖typeINormalizedFourier sigma t 0‖)) =
      (Q : ℝ) ^ (1 - sigma) *
        (|t| ^ j * ‖typeINormalizedFourier sigma t 0‖) := by
          rw [← hQP]
          ring_nf
    _ ≤ (Q : ℝ) ^ (1 - sigma) * C := by
      gcongr
      exact hDecay t

/-- Far-frequency decay after restoring the exact source normalization. -/
theorem exists_sourceScalar_farModes_bound (sigma : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (Q M : ℕ),
      0 < Q → 0 < M →
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedFarTail sigma t Q M‖ ≤
        (Q : ℝ) ^ (-sigma) *
          (K * (1 + |t|) ^ (n + 2) /
            ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n)) := by
  obtain ⟨K, hK, hFar⟩ := typeINormalizedFarTail_bound_order sigma n
  refine ⟨K, hK, ?_⟩
  intro t Q M hQ hM
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [norm_mul, norm_typeISourceNormalizationScalar sigma t (Q : ℝ) hQReal]
  exact mul_le_mul_of_nonneg_left (hFar t Q M hQ hM)
    (Real.rpow_nonneg hQReal.le _)

/-- Removing the zero, wrong-sign, and far-frequency terms from the exact
Poisson decomposition leaves a genuinely large negative reflected block. -/
theorem sourceSmoothBlock_large_forces_negativeModes
    {Y A r M : ℕ} {sigma t V : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hV : 0 ≤ V)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8) :
    V / 2 ≤
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeModes sigma t (2 ^ r * Y) M‖ := by
  let Q : ℕ := 2 ^ r * Y
  let z : ℂ := ((Q : ℂ) * typeINormalizedFourier sigma t 0)
  let neg : ℂ := typeINormalizedNegativeModes sigma t Q M
  let pos : ℂ := typeINormalizedPositiveModes sigma t Q M
  let far : ℂ := typeINormalizedFarTail sigma t Q M
  let c : ℂ := typeISourceNormalizationScalar sigma t Q
  have hDecomp := typeISourceSmoothBlock_eq_mode_decomposition_of_interior
    hY hLower hUpper (M := M) (sigma := sigma) (t := t)
  have hTriangle : ‖typeISourceSmoothBlock Y A r sigma t‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by
    rw [hDecomp]
    change ‖c * (z + neg + pos + far)‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖
    rw [mul_add, mul_add, mul_add]
    calc
      ‖c * z + c * neg + c * pos + c * far‖ ≤
          ‖c * z + c * neg + c * pos‖ + ‖c * far‖ := norm_add_le _ _
      _ ≤ (‖c * z + c * neg‖ + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖c * z‖ + ‖c * neg‖) + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by ring
  have hTotal : V ≤ ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ :=
    hLarge.trans hTriangle
  have hz : ‖c * z‖ ≤ V / 8 := by simpa only [Q, z, c] using hZero
  have hp : ‖c * pos‖ ≤ V / 8 := by simpa only [Q, pos, c] using hPositive
  have hf : ‖c * far‖ ≤ V / 8 := by simpa only [Q, far, c] using hFar
  have : V / 2 ≤ ‖c * neg‖ := by linarith
  simpa only [Q, neg, c] using this

/-- Once the zero, positive, and genuinely far Poisson terms have been
removed, the negative modes may be restricted further to a literal
stationary annulus.  The low- and high-frequency errors are stated as norms
of the exact interval sums, so the conclusion retains cancellation within
each of the three pieces and does not pass through a pointwise mode bound. -/
theorem sourceSmoothBlock_large_forces_negative_stationary_interval
    {Y A r M P J : ℕ} {sigma t V : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hPJ : P ≤ 2 ^ J * P) (hJM : 2 ^ J * P ≤ M)
    (hV : 0 ≤ V)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hLow :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y) 0 P‖ ≤ V / 8)
    (hHigh :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y)
          (2 ^ J * P) M‖ ≤ V / 8) :
    V / 4 ≤
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y)
          P (2 ^ J * P)‖ := by
  have hNegative := sourceSmoothBlock_large_forces_negativeModes
    hY hLower hUpper hV hLarge hZero hPositive hFar
  have hSplit := typeINormalizedNegativeModes_eq_three_intervals
    sigma t (2 ^ r * Y) P (2 ^ J * P) M hPJ hJM
  let c : ℂ := typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ)
  let low : ℂ := typeINormalizedNegativeInterval sigma t
    (2 ^ r * Y) 0 P
  let central : ℂ := typeINormalizedNegativeInterval sigma t
    (2 ^ r * Y) P (2 ^ J * P)
  let high : ℂ := typeINormalizedNegativeInterval sigma t
    (2 ^ r * Y) (2 ^ J * P) M
  have hTriangle :
      ‖c * typeINormalizedNegativeModes sigma t (2 ^ r * Y) M‖ ≤
        ‖c * low‖ + ‖c * central‖ + ‖c * high‖ := by
    rw [hSplit]
    change ‖c * (low + central + high)‖ ≤ _
    rw [mul_add, mul_add]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have hTotal : V / 2 ≤ ‖c * low‖ + ‖c * central‖ + ‖c * high‖ := by
    exact hNegative.trans (by simpa only [c] using hTriangle)
  have hLow' : ‖c * low‖ ≤ V / 8 := by
    simpa only [c, low] using hLow
  have hHigh' : ‖c * high‖ ≤ V / 8 := by
    simpa only [c, high] using hHigh
  have : V / 4 ≤ ‖c * central‖ := by linarith
  simpa only [c, central] using this

/-- The stationary interval isolated above feeds the exact interval Mellin
identity and hence produces one fixed-coefficient reflected polynomial at a
bounded ordinate displacement.  This is the cancellation-preserving source
entry for the later family extraction theorem. -/
theorem exists_large_stationary_reflected_interval_of_source
    {Y A r M P J : ℕ} {sigma t V H R K E : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hP : 0 < P) (hJ : 0 < J) (hJM : 2 ^ J * P ≤ M)
    (hsigma : 0 ≤ sigma) (hV : 0 ≤ V) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hLow :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y) 0 P‖ ≤ V / 8)
    (hHigh :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y)
          (2 ^ J * P) M‖ ≤ V / 8)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
        (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedIntervalMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) P (2 ^ J * P) u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
              (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hGap :
      ((2 ^ r * Y : ℕ) : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
        Real.pi * V / 2) :
    ∃ u ∈ Set.Icc (-H) H,
      R < ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 ^ J * P)‖ := by
  have hPJ : P ≤ 2 ^ J * P :=
    Nat.le_mul_of_pos_left P (pow_pos (by omega : 0 < 2) J)
  have hStationary := sourceSmoothBlock_large_forces_negative_stationary_interval
    hY hLower hUpper hPJ hJM hV hLarge hZero hPositive hFar hLow hHigh
  have hQ : 0 < 2 ^ r * Y := by positivity
  have hLU : P < 2 ^ J * P := by
    have hTwoPow : 1 < 2 ^ J := one_lt_pow₀ (by omega) (Nat.ne_of_gt hJ)
    nlinarith
  have hIdentity := sourceScalar_mul_negativeInterval_eq_reflectedMellinIntegral
    (sigma := sigma) (t := t) (Q := 2 ^ r * Y)
      (L := P) (U := 2 ^ J * P) hsigma hQ hLU
  have hNorm := congrArg norm hIdentity
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))] at hNorm
  have hIntegralLarge : Real.pi * V / 2 ≤
      ‖∫ u : ℝ,
        typeIReflectedIntervalMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) P (2 ^ J * P) u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
              (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ := by
    rw [hNorm] at hStationary
    have hTwoPiPos : 0 < 2 * Real.pi := by positivity
    have hScaled := mul_le_mul_of_nonneg_left hStationary hTwoPiPos.le
    field_simp at hScaled
    have hScaled' : 2 * Real.pi * V ≤
        4 * ‖∫ u : ℝ,
          typeIReflectedIntervalMellinPolynomial sigma t
              ((2 ^ r * Y : ℕ) : ℝ) P (2 ^ J * P) u *
            typeIDyadicCutoffMellin u *
              typeIPowerReflectionIntegral sigma (t + u)
                ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
                (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ := by
      convert hScaled using 1
      ring_nf
    nlinarith [Real.pi_pos]
  exact exists_large_typeIReflectedIntervalFixedPolynomial_of_integral
    hsigma (by exact_mod_cast hQ) hLU hH hR hKernel hIntegralLarge hTail hGap

/-- If only the zero frequency and the genuinely far frequencies are
discarded, one of the two retained signed Poisson halves carries a fixed
fraction of the original smooth Type-I large value.  This is the
cancellation-safe alternative used in the endpoint proof: the positive
half is not estimated term-by-term and hence no factor depending on the
dual cutoff is introduced. -/
theorem sourceSmoothBlock_large_forces_signedModes
    {Y A r M : ℕ} {sigma t V : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hV : 0 ≤ V)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8) :
    V / 4 ≤
        ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
          typeINormalizedNegativeModes sigma t (2 ^ r * Y) M‖ ∨
      V / 4 ≤
        ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
          typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ := by
  let Q : ℕ := 2 ^ r * Y
  let z : ℂ := (Q : ℂ) * typeINormalizedFourier sigma t 0
  let neg : ℂ := typeINormalizedNegativeModes sigma t Q M
  let pos : ℂ := typeINormalizedPositiveModes sigma t Q M
  let far : ℂ := typeINormalizedFarTail sigma t Q M
  let c : ℂ := typeISourceNormalizationScalar sigma t Q
  have hDecomp := typeISourceSmoothBlock_eq_mode_decomposition_of_interior
    hY hLower hUpper (M := M) (sigma := sigma) (t := t)
  have hTriangle : ‖typeISourceSmoothBlock Y A r sigma t‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by
    rw [hDecomp]
    change ‖c * (z + neg + pos + far)‖ ≤
      ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖
    rw [mul_add, mul_add, mul_add]
    calc
      ‖c * z + c * neg + c * pos + c * far‖ ≤
          ‖c * z + c * neg + c * pos‖ + ‖c * far‖ := norm_add_le _ _
      _ ≤ (‖c * z + c * neg‖ + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖c * z‖ + ‖c * neg‖) + ‖c * pos‖) + ‖c * far‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ := by ring
  have hTotal : V ≤ ‖c * z‖ + ‖c * neg‖ + ‖c * pos‖ + ‖c * far‖ :=
    hLarge.trans hTriangle
  have hz : ‖c * z‖ ≤ V / 8 := by simpa only [Q, z, c] using hZero
  have hf : ‖c * far‖ ≤ V / 8 := by simpa only [Q, far, c] using hFar
  by_contra h
  push Not at h
  have hn : ‖c * neg‖ < V / 4 := by simpa only [Q, neg, c] using h.1
  have hp : ‖c * pos‖ < V / 4 := by simpa only [Q, pos, c] using h.2
  linarith

/-! ## Source block to a genuine reflected large value -/

/-- A large interior source block, after the zero, wrong-sign, and far
Poisson modes have been removed quantitatively, produces a large value of
the actual fixed-coefficient reflected polynomial at a bounded ordinate
displacement.  The final hypothesis is the exact normalization needed to
pass from the weighted reflected polynomial to the coefficient-bounded wide
Dirichlet polynomial used by Montgomery--Halasz--Huxley. -/
theorem exists_shift_large_normalized_reflected_wide
    {Y A r M : ℕ} {sigma t V H R K E S : ℝ}
    (hY : 0 < Y)
    (hLower : (((Y + 1 : ℕ) : ℝ)) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hsigma : 0 ≤ sigma) (hM : 1 < M)
    (hV : 0 ≤ V) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hKernel : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTail :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hGap :
      ((2 ^ r * Y : ℕ) : ℝ) * R * K *
          typeIDyadicCutoffMellinL1 + E < Real.pi * V)
    (hNormalize :
      S + (M : ℝ) ^ (-sigma) ≤ R / (M : ℝ) ^ sigma) :
    ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖ := by
  have hQ : 0 < 2 ^ r * Y := by positivity
  have hQReal : (0 : ℝ) < (2 ^ r * Y : ℕ) := by exact_mod_cast hQ
  have hMOne : 1 ≤ M := hM.le
  have hNeg := sourceSmoothBlock_large_forces_negativeModes
    hY hLower hUpper hV hLarge hZero hPositive hFar
  have hIntegralNorm :=
    norm_typeIReflectedMellinIntegral_eq_two_pi_mul_negativeModes
      (t := t) hsigma hQ hMOne
  have hIntegralLarge : Real.pi * V ≤
      ‖∫ u : ℝ,
        typeIReflectedMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ := by
    rw [hIntegralNorm]
    nlinarith [Real.pi_pos]
  obtain ⟨u, hu, huLarge⟩ :=
    exists_large_typeIReflectedFixedPolynomial_of_integral
      hsigma hQReal hMOne hH hR hKernel hIntegralLarge hTail hGap
  refine ⟨u, hu, ?_⟩
  have hMReal : (0 : ℝ) < M := by exact_mod_cast (lt_trans Nat.zero_lt_one hM)
  have hDenom : 0 < (M : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos hMReal sigma
  have hFixedDiv : R / (M : ℝ) ^ sigma <
      ‖typeIReflectedFixedPolynomial sigma (t + u) M /
        (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDenom, div_lt_div_iff₀ hDenom hDenom]
    simpa only [mul_comm] using mul_lt_mul_of_pos_right huLarge hDenom
  have hIdentity := wideDirichletPoly_normalizedTypeIReflectedCoeff
    (sigma := sigma) (u := t + u) hM
  let P : ℂ := wideDirichletPoly 1 (Nat.clog 2 M)
    (normalizedTypeIReflectedCoeff sigma M) (-(t + u))
  let z : ℂ := (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)
  have hRearrange :
      typeIReflectedFixedPolynomial sigma (t + u) M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ) = P + z := by
    dsimp only [P, z]
    calc
      typeIReflectedFixedPolynomial sigma (t + u) M /
            (((M : ℝ) ^ sigma : ℝ) : ℂ) =
          (typeIReflectedFixedPolynomial sigma (t + u) M /
              (((M : ℝ) ^ sigma : ℝ) : ℂ) -
            (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by ring
      _ = wideDirichletPoly 1 (Nat.clog 2 M)
            (normalizedTypeIReflectedCoeff sigma M) (-(t + u)) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by rw [← hIdentity]
  have hTriangle :
      ‖typeIReflectedFixedPolynomial sigma (t + u) M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ ≤
        ‖P‖ + (M : ℝ) ^ (-sigma) := by
    rw [hRearrange]
    calc
      ‖P + z‖ ≤ ‖P‖ + ‖z‖ := norm_add_le _ _
      _ = ‖P‖ + (M : ℝ) ^ (-sigma) := by
        dsimp only [z]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hMReal.le _)]
  dsimp only [P] at hTriangle ⊢
  linarith

/-- Algebraic normalization from a large fixed reflected polynomial to the
coefficient-bounded wide polynomial.  This lemma is sign-neutral: the caller
supplies the actual reflected ordinate. -/
theorem large_normalized_reflected_wide_of_fixed
    {M : ℕ} {sigma u R S : ℝ} (hM : 1 < M)
    (hNormalize : S + (M : ℝ) ^ (-sigma) ≤ R / (M : ℝ) ^ sigma)
    (hLarge : R < ‖typeIReflectedFixedPolynomial sigma u M‖) :
    S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
      (normalizedTypeIReflectedCoeff sigma M) (-u)‖ := by
  have hMReal : (0 : ℝ) < M := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hM)
  have hDenom : 0 < (M : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos hMReal sigma
  have hFixedDiv : R / (M : ℝ) ^ sigma <
      ‖typeIReflectedFixedPolynomial sigma u M /
        (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDenom, div_lt_div_iff₀ hDenom hDenom]
    simpa only [mul_comm] using mul_lt_mul_of_pos_right hLarge hDenom
  have hIdentity := wideDirichletPoly_normalizedTypeIReflectedCoeff
    (sigma := sigma) (u := u) hM
  let P : ℂ := wideDirichletPoly 1 (Nat.clog 2 M)
    (normalizedTypeIReflectedCoeff sigma M) (-u)
  let z : ℂ := (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)
  have hRearrange :
      typeIReflectedFixedPolynomial sigma u M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ) = P + z := by
    dsimp only [P, z]
    calc
      typeIReflectedFixedPolynomial sigma u M /
            (((M : ℝ) ^ sigma : ℝ) : ℂ) =
          (typeIReflectedFixedPolynomial sigma u M /
              (((M : ℝ) ^ sigma : ℝ) : ℂ) -
            (((M : ℝ) ^ (-sigma) : ℝ) : ℂ)) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by ring
      _ = wideDirichletPoly 1 (Nat.clog 2 M)
            (normalizedTypeIReflectedCoeff sigma M) (-u) +
              (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by rw [← hIdentity]
  have hTriangle :
      ‖typeIReflectedFixedPolynomial sigma u M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ)‖ ≤
        ‖P‖ + (M : ℝ) ^ (-sigma) := by
    rw [hRearrange]
    calc
      ‖P + z‖ ≤ ‖P‖ + ‖z‖ := norm_add_le _ _
      _ = ‖P‖ + (M : ℝ) ^ (-sigma) := by
        dsimp only [z]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hMReal.le _)]
  dsimp only [P] at hTriangle ⊢
  linarith

/-- A large interior source block yields one of the two actual normalized
reflected wide polynomials.  The zero and far modes are removed once, and
the sign is selected only after the exact Poisson identity. -/
theorem exists_signed_shift_large_normalized_reflected_wide
    {Y A r M : ℕ} {sigma t V H R K E S : ℝ}
    (hY : 0 < Y)
    (hLower : (((Y + 1 : ℕ) : ℝ)) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hsigma : 0 ≤ sigma) (hM : 1 < M)
    (hV : 0 ≤ V) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hKernelNeg : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hKernelPos : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (-t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTailNeg :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hTailPos :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial sigma (-t)
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (-t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hGap :
      ((2 ^ r * Y : ℕ) : ℝ) * R * K *
          typeIDyadicCutoffMellinL1 + E < Real.pi * V / 2)
    (hNormalize :
      S + (M : ℝ) ^ (-sigma) ≤ R / (M : ℝ) ^ sigma) :
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t - u)‖) := by
  have hQ : 0 < 2 ^ r * Y := by positivity
  have hMOne : 1 ≤ M := hM.le
  rcases sourceSmoothBlock_large_forces_signedModes
      hY hLower hUpper hV hLarge hZero hFar with hNeg | hPos
  · left
    have hGap' :
        ((2 ^ r * Y : ℕ) : ℝ) * R * K *
            typeIDyadicCutoffMellinL1 + E < 2 * Real.pi * (V / 4) := by
      convert hGap using 1
      ring_nf
    obtain ⟨u, hu, hFixed⟩ :=
      exists_large_reflectedFixedPolynomial_of_negativeModes
        hsigma hQ hMOne hH hR hNeg hKernelNeg hTailNeg hGap'
    exact ⟨u, hu,
      large_normalized_reflected_wide_of_fixed hM hNormalize hFixed⟩
  · right
    have hGap' :
        ((2 ^ r * Y : ℕ) : ℝ) * R * K *
            typeIDyadicCutoffMellinL1 + E < 2 * Real.pi * (V / 4) := by
      convert hGap using 1
      ring_nf
    obtain ⟨u, hu, hFixed⟩ :=
      exists_large_reflectedFixedPolynomial_of_positiveModes
        hsigma hQ hMOne hH hR hPos hKernelPos hTailPos hGap'
    have hWide := large_normalized_reflected_wide_of_fixed
      hM hNormalize hFixed
    refine ⟨u, hu, ?_⟩
    convert hWide using 1
    ring_nf

/-- Translating the ordinate of a wide polynomial is exactly the same
unimodular twist of its coefficients as for an ordinary dyadic block. -/
theorem wideDirichletPoly_translate
    (Q k : ℕ) (a : ℕ → ℂ) (c t : ℝ) :
    wideDirichletPoly Q k a (t + c) =
      wideDirichletPoly Q k (phaseShiftCoeffs c a) t := by
  unfold wideDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    exact lt_of_le_of_lt (Nat.zero_le Q) (Finset.mem_Ioc.mp hn).1
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [phaseShiftCoeffs, ite_eq_right hnPos.ne', mul_assoc,
    ← Complex.cpow_add _ _ hnNe]
  congr 2
  push_cast
  ring

/-- Bounded pointwise displacement followed by unit-bin selection.  The
weight on an image point is its complete fibre cardinality, so collisions
cannot silently discard multiplicity. -/
theorem exists_separated_bounded_shift_image_medium
    (W : Finset ℝ) (shift : ℝ → ℝ) (H : ℝ)
    (_hH : 0 ≤ H) (hSeparated : IsSeparated 1 W)
    (hShift : ∀ t ∈ W, |t - shift t| ≤ H) :
    ∃ U ⊆ W.image shift, IsSeparated 1 U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card := by
  classical
  let weight : ℝ → ℕ := fun _ => 1
  let shiftedWeight : ℝ → ℕ := fun u =>
    ∑ t ∈ W.filter (fun x => shift x = u), weight t
  have hLocalOriginal : ∀ z : ℤ,
      ∑ t ∈ W.filter
          (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1), weight t ≤ 1 := by
    intro z
    have hCard :
        (W.filter (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1)).card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro x y hx hy
      simp only [Finset.mem_filter] at hx hy
      by_contra hxy
      have hSep := hSeparated x hx.1 y hy.1 hxy
      rw [Real.dist_eq] at hSep
      have hlt : |x - y| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
      linarith
    simpa [weight] using hCard
  have hLocalShifted : ∀ z : ℤ,
      ∑ u ∈ (W.image shift).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1), shiftedWeight u ≤
        2 * ⌈H⌉₊ + 1 := by
    intro z
    simpa only [shiftedWeight, weight, mul_one] using
      shifted_bin_weight_le_of_unit_bin_weight W weight id shift H 1
        (by simpa only [id_eq] using hShift) hLocalOriginal z
  obtain ⟨U, hUImage, hUSep, hWeight⟩ :=
    weighted_separated_selection (W.image shift) shiftedWeight
      (2 * ⌈H⌉₊ + 1) hLocalShifted
  have hAll : W.filter (fun t => shift t ∈ W.image shift) = W := by
    apply Finset.filter_eq_self.mpr
    intro t ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter W (W.image shift)
    shift weight
  rw [hAll] at hFiber
  have hTotal : ∑ u ∈ W.image shift, shiftedWeight u = W.card := by
    simpa [shiftedWeight, weight] using hFiber
  refine ⟨U, hUImage, hUSep, ?_⟩
  rw [← hTotal]
  simpa only [mul_assoc] using hWeight

/-- Family extraction from a genuine stationary annulus.  The common dyadic
index is chosen before bounded-displacement reseparation, so both the complete
fibre multiplicity and the fixed `T / N` scale are retained. -/
theorem extract_common_negative_reflected_stationary_block
    {P J : ℕ} {sigma T D H R : ℝ} (W : Finset ℝ)
    (hP : 0 < P) (hJ : 0 < J) (hW : W.Nonempty)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      R ≤ ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 ^ J * P)‖) :
    ∃ j ∈ Finset.range J, ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ J * (2 * (2 * ⌈H⌉₊ + 1)) * U.card ∧
      ∀ v ∈ U,
        (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
          ‖dirichletPoly (2 ^ j * P)
            (phaseShiftCoeffs (-3 * T)
              (normalizedTypeIReflectedCoeff sigma
                (2 ^ (j + 1) * P))) v‖ := by
  classical
  have hEachScale : ∀ t ∈ W, ∃ j ∈ Finset.range J,
      ∃ u ∈ Set.Icc (-H) H,
        (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
          ‖dirichletPoly (2 ^ j * P)
            (normalizedTypeIReflectedCoeff sigma
              (2 ^ (j + 1) * P)) (-(t + u))‖ := by
    intro t ht
    obtain ⟨u, hu, hLarge⟩ := hEach t ht
    obtain ⟨j, hj, hjLarge⟩ :=
      exists_large_normalized_reflected_interval_dyadic_block hP hJ hLarge
    exact ⟨j, hj, u, hu, hjLarge⟩
  let scale : ℝ → ℕ := fun t =>
    if ht : t ∈ W then Classical.choose (hEachScale t ht) else 0
  have hScaleMem : ∀ t ∈ W, scale t ∈ Finset.range J := by
    intro t ht
    simp only [scale, dite_eq_left ht]
    exact (Classical.choose_spec (hEachScale t ht)).1
  obtain ⟨j, hj, hScaleCard⟩ := weighted_finite_pigeonhole W
    (Finset.range J) (fun _ => 1) scale hW hScaleMem
  let Wj := W.filter (fun t => scale t = j)
  have hWjSub : Wj ⊆ W := Finset.filter_subset _ _
  have hWjSep : IsSeparated 1 Wj := by
    intro x hx y hy hxy
    exact hSeparated x (hWjSub hx) y (hWjSub hy) hxy
  have hWCard : W.card ≤ J * Wj.card := by
    simpa [Wj] using hScaleCard
  have hWjEach : ∀ t ∈ Wj, ∃ u ∈ Set.Icc (-H) H,
      (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
        ‖dirichletPoly (2 ^ j * P)
          (normalizedTypeIReflectedCoeff sigma
            (2 ^ (j + 1) * P)) (-(t + u))‖ := by
    intro t ht
    have htData := Finset.mem_filter.mp ht
    have hChosen := (Classical.choose_spec (hEachScale t htData.1)).2
    have hScaleEq : Classical.choose (hEachScale t htData.1) = j := by
      simpa only [scale, dite_eq_left htData.1] using htData.2
    simpa only [hScaleEq] using hChosen
  let reflect : ℝ → ℝ := fun t => 3 * T - t
  let Wrev : Finset ℝ := Wj.image reflect
  have hReflectInj : Function.Injective reflect := by
    intro x y hxy
    dsimp only [reflect] at hxy
    linarith
  have hWrevCard : Wrev.card = Wj.card := by
    dsimp only [Wrev]
    exact Finset.card_image_iff.mpr fun _ _ _ _ hxy => hReflectInj hxy
  have hWrevSep : IsSeparated 1 Wrev := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨tx, htx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ty, hty, hyEq⟩
    have htxy : tx ≠ ty := by
      intro h
      subst ty
      exact hxy hyEq
    have hsep := hWjSep tx htx ty hty htxy
    subst y
    rw [Real.dist_eq] at hsep ⊢
    dsimp only [reflect]
    rw [show 3 * T - tx - (3 * T - ty) = -(tx - ty) by ring, abs_neg]
    exact hsep
  have hOriginalMem : ∀ x ∈ Wrev, 3 * T - x ∈ Wj := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    convert ht using 1
    dsimp only [reflect]
    ring
  let displacement : ℝ → ℝ := fun x =>
    if hx : x ∈ Wrev then Classical.choose
      (hWjEach (3 * T - x) (hOriginalMem x hx)) else 0
  have hDispMem : ∀ x ∈ Wrev,
      displacement x ∈ Set.Icc (-H) H := by
    intro x hx
    simp only [displacement, dite_eq_left hx]
    exact (Classical.choose_spec
      (hWjEach (3 * T - x) (hOriginalMem x hx))).1
  let shift : ℝ → ℝ := fun x => x - displacement x
  have hShiftBound : ∀ x ∈ Wrev, |x - shift x| ≤ H := by
    intro x hx
    have hd := hDispMem x hx
    dsimp only [shift]
    rw [show x - (x - displacement x) = displacement x by ring]
    exact abs_le.mpr hd
  obtain ⟨U, hUImage, hUSep, hShiftCard⟩ :=
    exists_separated_bounded_shift_image_medium Wrev shift H hH
      hWrevSep hShiftBound
  refine ⟨j, hj, U, hUSep, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨x, hx, rfl⟩
    have hxRange := hRange (3 * T - x) (hWjSub (hOriginalMem x hx))
    have hdu := hDispMem x hx
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift]
    · linarith [hdu.2]
    · linarith [hdu.1]
  · calc
      W.card ≤ J * Wj.card := hWCard
      _ = J * Wrev.card := by rw [hWrevCard]
      _ ≤ J * (2 * (2 * ⌈H⌉₊ + 1) * U.card) := by gcongr
      _ = J * (2 * (2 * ⌈H⌉₊ + 1)) * U.card := by ring
  · intro v hv
    rcases Finset.mem_image.mp (hUImage hv) with ⟨x, hx, rfl⟩
    have hLarge := (Classical.choose_spec
      (hWjEach (3 * T - x) (hOriginalMem x hx))).2
    have hDispEq : displacement x = Classical.choose
        (hWjEach (3 * T - x) (hOriginalMem x hx)) := by
      simp only [displacement, dite_eq_left hx]
    rw [← hDispEq] at hLarge
    have hArg : -((3 * T - x) + displacement x) = shift x + (-3 * T) := by
      dsimp only [shift]
      ring
    rw [hArg, dirichletPoly_translate] at hLarge
    exact hLarge

/-- Family-level source entry for the stationary B-process.  Every analytic
error estimate is still attached to the ordinate where it is used, while the
physical source scale, stationary annulus, Mellin window, and threshold are
common.  The conclusion performs both nontrivial finite selections: first a
dyadic reflected interval and then a one-separated bounded-displacement
subfamily. -/
theorem extract_common_stationary_reflected_block_of_source
    {Y A r M P J : ℕ} {sigma T D H V R K E : ℝ} (W : Finset ℝ)
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hP : 0 < P) (hJ : 0 < J) (hJM : 2 ^ J * P ≤ M)
    (hsigma : 0 ≤ sigma) (hV : 0 ≤ V) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hW : W.Nonempty) (hT : 0 ≤ T) (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hLarge : ∀ t ∈ W, V ≤ ‖typeISourceSmoothBlock Y A r sigma t‖)
    (hZero : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier sigma t 0)‖ ≤ V / 8)
    (hPositive : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedPositiveModes sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hFar : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail sigma t (2 ^ r * Y) M‖ ≤ V / 8)
    (hLow : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y) 0 P‖ ≤ V / 8)
    (hHigh : ∀ t ∈ W,
      ‖typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        typeINormalizedNegativeInterval sigma t (2 ^ r * Y)
          (2 ^ J * P) M‖ ≤ V / 8)
    (hKernel : ∀ t ∈ W, ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral sigma (t + u)
        ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
        (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTail : ∀ t ∈ W,
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedIntervalMellinPolynomial sigma t
            ((2 ^ r * Y : ℕ) : ℝ) P (2 ^ J * P) u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral sigma (t + u)
              ((((P + 1 : ℕ) : ℝ) * (2 ^ r * Y : ℕ)) / 2)
              (2 * ((2 ^ J * P : ℕ) : ℝ) * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hGap : ((2 ^ r * Y : ℕ) : ℝ) * R * K *
        typeIDyadicCutoffMellinL1 + E < Real.pi * V / 2) :
    ∃ j ∈ Finset.range J, ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      W.card ≤ J * (2 * (2 * ⌈H⌉₊ + 1)) * U.card ∧
      ∀ v ∈ U,
        (R / J) / ((2 ^ (j + 1) * P : ℕ) : ℝ) ^ sigma ≤
          ‖dirichletPoly (2 ^ j * P)
            (phaseShiftCoeffs (-3 * T)
              (normalizedTypeIReflectedCoeff sigma
                (2 ^ (j + 1) * P))) v‖ := by
  have hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      R ≤ ‖typeIReflectedIntervalFixedPolynomial sigma (t + u)
        P (2 ^ J * P)‖ := by
    intro t ht
    obtain ⟨u, hu, hLargeAt⟩ :=
      exists_large_stationary_reflected_interval_of_source
        hY hLower hUpper hP hJ hJM hsigma hV hH hR
        (hLarge t ht) (hZero t ht) (hPositive t ht) (hFar t ht)
        (hLow t ht) (hHigh t ht) (hKernel t ht) (hTail t ht) hGap
    exact ⟨u, hu, hLargeAt.le⟩
  exact extract_common_negative_reflected_stationary_block
    W hP hJ hW hH hT hDH hSeparated hRange hEach

/-- Family form of the reflected extraction.  Each source ordinate may
choose its own bounded Mellin displacement, but the output is reseparated,
translated to one positive base interval, and pigeonholed onto one common
ordinary dyadic block.  The displayed cardinality loss keeps every fibre of
the displacement map. -/
theorem extract_common_reflected_mhh_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
      W.card ≤
        (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
      ∀ v ∈ U,
        S / Nat.clog 2 M ≤
          ‖dirichletPoly (2 ^ j)
            (phaseShiftCoeffs (-3 * T)
              (normalizedTypeIReflectedCoeff sigma M)) v‖ := by
  classical
  let reflect : ℝ → ℝ := fun t => 3 * T - t
  let Wrev : Finset ℝ := W.image reflect
  have hreflectInj : Function.Injective reflect := by
    intro x y hxy
    dsimp only [reflect] at hxy
    linarith
  have hWrevCard : Wrev.card = W.card := by
    dsimp only [Wrev]
    exact Finset.card_image_iff.mpr fun _ hx _ hy hxy =>
      hreflectInj hxy
  have hWrevSeparated : IsSeparated 1 Wrev := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨tx, htx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ty, hty, hyEq⟩
    have htxy : tx ≠ ty := by
      intro h
      subst ty
      exact hxy hyEq
    have hsep := hSeparated tx htx ty hty htxy
    subst y
    rw [Real.dist_eq] at hsep ⊢
    dsimp only [reflect]
    rw [show 3 * T - tx - (3 * T - ty) = -(tx - ty) by ring, abs_neg]
    exact hsep
  have hOriginalMem : ∀ x ∈ Wrev, 3 * T - x ∈ W := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    convert ht using 1
    dsimp only [reflect]
    ring
  let displacement : ℝ → ℝ := fun x =>
    if hx : x ∈ Wrev then Classical.choose (hEach (3 * T - x)
      (hOriginalMem x hx)) else 0
  have hDisplacementMem : ∀ x ∈ Wrev,
      displacement x ∈ Set.Icc (-H) H := by
    intro x hx
    simp only [displacement, dite_eq_left hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).1
  have hDisplacementLarge : ∀ x ∈ Wrev,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M)
          (-((3 * T - x) + displacement x))‖ := by
    intro x hx
    simp only [displacement, dite_eq_left hx]
    exact (Classical.choose_spec (hEach (3 * T - x)
      (hOriginalMem x hx))).2
  let shift : ℝ → ℝ := fun x => x - displacement x
  have hShiftBound : ∀ x ∈ Wrev, |x - shift x| ≤ H := by
    intro x hx
    have hd := hDisplacementMem x hx
    dsimp only [shift]
    rw [show x - (x - displacement x) = displacement x by ring]
    exact abs_le.mpr hd
  obtain ⟨U₀, hU₀Image, hU₀Sep, hCardShift⟩ :=
    exists_separated_bounded_shift_image_medium Wrev shift H hH
      hWrevSeparated hShiftBound
  have hWide : ∀ v ∈ U₀,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M)) v‖ := by
    intro v hv
    have hvImage := hU₀Image hv
    rcases Finset.mem_image.mp hvImage with ⟨x, hx, rfl⟩
    have hLarge := hDisplacementLarge x hx
    have hArg : -((3 * T - x) + displacement x) =
        shift x + (-3 * T) := by
      dsimp only [shift]
      ring
    rw [hArg, wideDirichletPoly_translate] at hLarge
    exact hLarge
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  obtain ⟨j, hj, U, hUsub, hCardDyadic, hLargeDyadic⟩ :=
    exists_dyadic_block_and_subset 1 (Nat.clog 2 M)
      (phaseShiftCoeffs (-3 * T)
        (normalizedTypeIReflectedCoeff sigma M)) U₀ S hClog
      (fun v hv => (hWide v hv).le)
  refine ⟨j, hj, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hU₀Sep x (hUsub hx) y (hUsub hy) hxy
  · intro v hv
    have hvU₀ := hUsub hv
    have hvImage := hU₀Image hvU₀
    rcases Finset.mem_image.mp hvImage with ⟨x, hx, rfl⟩
    have hxRange := hRange (3 * T - x) (hOriginalMem x hx)
    have hdu := hDisplacementMem x hx
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift]
    · have hduUpper : displacement x ≤ H := hdu.2
      linarith
    · have hduLower : -H ≤ displacement x := hdu.1
      linarith
  · intro v hv
    have hvU₀ := hUsub hv
    have hvImage := hU₀Image hvU₀
    rcases Finset.mem_image.mp hvImage with ⟨x, hx, rfl⟩
    have hxRange := hRange (3 * T - x) (hOriginalMem x hx)
    have hdu := hDisplacementMem x hx
    dsimp only [shift]
    constructor
    · linarith [hdu.2]
    · linarith [hdu.1]
  · rw [← hWrevCard]
    calc
      Wrev.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U₀.card := hCardShift
      _ ≤ 2 * (2 * ⌈H⌉₊ + 1) *
          ((Nat.clog 2 M) * U.card) := by
            gcongr
            exact_mod_cast hCardDyadic
      _ = (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card := by ring
  · intro v hv
    simpa only [mul_one] using hLargeDyadic v hv

/-- Positive-sign companion to `extract_common_reflected_mhh_block`.
The positive Poisson half already lands at the positive ordinate `t - u`,
so no reflection about `3T/2` and no coefficient phase shift are needed. -/
theorem extract_common_positive_reflected_mhh_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t - u)‖) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
      (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
      W.card ≤
        (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
      ∀ v ∈ U,
        S / Nat.clog 2 M ≤
          ‖dirichletPoly (2 ^ j)
            (normalizedTypeIReflectedCoeff sigma M) v‖ := by
  classical
  let displacement : ℝ → ℝ := fun t =>
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hDisplacementMem : ∀ t ∈ W,
      displacement t ∈ Set.Icc (-H) H := by
    intro t ht
    simp only [displacement, dite_eq_left ht]
    exact (Classical.choose_spec (hEach t ht)).1
  have hDisplacementLarge : ∀ t ∈ W,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M)
          (t - displacement t)‖ := by
    intro t ht
    simp only [displacement, dite_eq_left ht]
    exact (Classical.choose_spec (hEach t ht)).2
  let shift : ℝ → ℝ := fun t => t - displacement t
  have hShiftBound : ∀ t ∈ W, |t - shift t| ≤ H := by
    intro t ht
    have hd := hDisplacementMem t ht
    dsimp only [shift]
    rw [show t - (t - displacement t) = displacement t by ring]
    exact abs_le.mpr hd
  obtain ⟨U₀, hU₀Image, hU₀Sep, hCardShift⟩ :=
    exists_separated_bounded_shift_image_medium W shift H hH
      hSeparated hShiftBound
  have hWide : ∀ v ∈ U₀,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) v‖ := by
    intro v hv
    rcases Finset.mem_image.mp (hU₀Image hv) with ⟨t, ht, rfl⟩
    exact hDisplacementLarge t ht
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  obtain ⟨j, hj, U, hUsub, hCardDyadic, hLargeDyadic⟩ :=
    exists_dyadic_block_and_subset 1 (Nat.clog 2 M)
      (normalizedTypeIReflectedCoeff sigma M) U₀ S hClog
      (fun v hv => (hWide v hv).le)
  refine ⟨j, hj, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hU₀Sep x (hUsub hx) y (hUsub hy) hxy
  · intro v hv
    have hvU₀ := hUsub hv
    rcases Finset.mem_image.mp (hU₀Image hvU₀) with ⟨t, ht, rfl⟩
    have htRange := hRange t ht
    have hdu := hDisplacementMem t ht
    rw [Set.mem_Icc]
    constructor <;> dsimp only [shift]
    · linarith [hdu.2]
    · linarith [hdu.1]
  · intro v hv
    have hvU₀ := hUsub hv
    rcases Finset.mem_image.mp (hU₀Image hvU₀) with ⟨t, ht, rfl⟩
    have htRange := hRange t ht
    have hdu := hDisplacementMem t ht
    dsimp only [shift]
    constructor
    · linarith [hdu.2]
    · linarith [hdu.1]
  · calc
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U₀.card := hCardShift
      _ ≤ 2 * (2 * ⌈H⌉₊ + 1) *
          ((Nat.clog 2 M) * U.card) := by
            gcongr
            exact_mod_cast hCardDyadic
      _ = (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card := by ring
  · intro v hv
    simpa only [mul_one] using hLargeDyadic v hv

/-- The common reflected block is an actual input to the unrestricted
Montgomery--Halasz--Huxley theorem.  This is the cardinality conclusion used
later by the medium witness consumer; in particular, the coefficients in the
MHH call are the normalized reflected coefficients produced by the exact
Poisson/Mellin chain above. -/
theorem reflected_family_mhh_cardinality
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (hDH : D + H ≤ T / 2) (hS : 0 < S)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖)
    (hsigma : 0 ≤ sigma) :
    ∃ K : ℝ, 0 < K ∧
      ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        W.card ≤
          (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
        (U.card : ℝ) ≤
          K * (1 + (((harmonic (2 ^ j) : ℚ) : ℝ))) *
            (((2 ^ j : ℕ) : ℝ) ^ 2 / (S / Nat.clog 2 M) ^ 2 +
              (3 * T) * min
                (((2 ^ j : ℕ) : ℝ) / (S / Nat.clog 2 M) ^ 2)
                (((2 ^ j : ℕ) : ℝ) ^ 4 /
                  (S / Nat.clog 2 M) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  obtain ⟨j, hj, U, hUSep, hUBase, _hURange, hCard, hLarge⟩ :=
    extract_common_reflected_mhh_block W hM hH (zero_le_one.trans hT) hDH
      hSeparated hRange hEach
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  have hThreshold : 0 < S / Nat.clog 2 M := by positivity
  have hCoeff : ∀ n ∈ dyadicInterval (2 ^ j),
      ‖phaseShiftCoeffs (-3 * T)
        (normalizedTypeIReflectedCoeff sigma M) n‖ ≤ 1 := by
    intro n _hn
    rw [norm_phaseShiftCoeffs]
    exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
      (lt_trans Nat.zero_lt_one hM)
  have hAt := hMHH (2 ^ j) (3 * T) (S / Nat.clog 2 M) U
    (phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma M))
    (pow_pos (by omega) j) (by linarith) hThreshold hCoeff hUSep hUBase
    (fun v hv => hLarge v hv)
  exact ⟨K, hK, j, hj, U, hUSep, hUBase, hCard, hAt⟩

/-- MHH cardinality conclusion for the retained positive Poisson half. -/
theorem positive_reflected_family_mhh_cardinality
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (hDH : D + H ≤ T / 2) (hS : 0 < S)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W, ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)
    (hsigma : 0 ≤ sigma) :
    ∃ K : ℝ, 0 < K ∧
      ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        W.card ≤
          (2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) * U.card ∧
        (U.card : ℝ) ≤
          K * (1 + (((harmonic (2 ^ j) : ℚ) : ℝ))) *
            (((2 ^ j : ℕ) : ℝ) ^ 2 / (S / Nat.clog 2 M) ^ 2 +
              (3 * T) * min
                (((2 ^ j : ℕ) : ℝ) / (S / Nat.clog 2 M) ^ 2)
                (((2 ^ j : ℕ) : ℝ) ^ 4 /
                  (S / Nat.clog 2 M) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  obtain ⟨j, hj, U, hUSep, hUBase, _hURange, hCard, hLarge⟩ :=
    extract_common_positive_reflected_mhh_block W hM hH
      (zero_le_one.trans hT) hDH hSeparated hRange hEach
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  have hThreshold : 0 < S / Nat.clog 2 M := by positivity
  have hCoeff : ∀ n ∈ dyadicInterval (2 ^ j),
      ‖normalizedTypeIReflectedCoeff sigma M n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
      (lt_trans Nat.zero_lt_one hM)
  have hAt := hMHH (2 ^ j) (3 * T) (S / Nat.clog 2 M) U
    (normalizedTypeIReflectedCoeff sigma M)
    (pow_pos (by omega) j) (by linarith) hThreshold hCoeff hUSep hUBase
    (fun v hv => hLarge v hv)
  exact ⟨K, hK, j, hj, U, hUSep, hUBase, hCard, hAt⟩

/-- A cancellation-safe family pigeonhole for the two retained Poisson
signs.  No point is discarded before the signed alternative is known; the
only loss is the explicit factor two. -/
theorem select_common_signed_reflected_family
    {M : ℕ} {sigma H S : ℝ} (W : Finset ℝ)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    (∃ W' : Finset ℝ, W' ⊆ W ∧ W.card ≤ 2 * W'.card ∧
      ∀ t ∈ W', ∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
    (∃ W' : Finset ℝ, W' ⊆ W ∧ W.card ≤ 2 * W'.card ∧
      ∀ t ∈ W', ∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖) := by
  classical
  let isNegative : ℝ → Prop := fun t =>
    ∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖
  let Wneg := W.filter isNegative
  by_cases hLargeHalf : W.card ≤ 2 * Wneg.card
  · left
    refine ⟨Wneg, Finset.filter_subset _ _, hLargeHalf, ?_⟩
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  · right
    let Wpos := W.filter (fun t => ¬ isNegative t)
    have hPartition : Wneg.card + Wpos.card = W.card := by
      simpa only [Wneg, Wpos, isNegative] using
        W.card_filter_add_card_filter_not isNegative
    have hCard : W.card ≤ 2 * Wpos.card := by omega
    refine ⟨Wpos, Finset.filter_subset _ _, hCard, ?_⟩
    intro t ht
    have htData := Finset.mem_filter.mp ht
    rcases hEach t htData.1 with hNeg | hPos
    · exact False.elim (htData.2 hNeg)
    · exact hPos

/-
/-- One cancellation-safe interface for the two retained Poisson signs.
The coefficient sequence is existential because the negative sign carries
the fixed translation by `-3T`, whereas the positive sign does not.  The
last field identifies its norm with the same normalized reflected block at
an actual positive ordinate in `[T/2,5T/2]`; this is the bridge needed by
the Weyl alternative after the finite sign and displacement selections. -/
theorem extract_common_signed_reflected_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      ∃ a : ℕ → ℂ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
        W.card ≤ 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
          (Nat.clog 2 M) * U.card ∧
        (∀ n ∈ dyadicInterval (2 ^ j), ‖a n‖ ≤ 1) ∧
        (∀ v ∈ U, S / Nat.clog 2 M ≤ ‖dirichletPoly (2 ^ j) a v‖) ∧
        (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
          ‖dirichletPoly (2 ^ j) a v‖ =
            ‖dirichletPoly (2 ^ j)
              (normalizedTypeIReflectedCoeff sigma M) w‖) := by
  rcases select_common_signed_reflected_family W hEach with
    ⟨Wsign, hWsign, hSignCard, hNegative⟩ |
      ⟨Wsign, hWsign, hSignCard, hPositive⟩
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hNegative
    let a : ℕ → ℂ := phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma M)
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      rw [norm_phaseShiftCoeffs]
      exact norm_normalizedTypeIReflectedCoeff_le_one (by linarith)
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨3 * T - v, ?_, ?_⟩
      · rw [Set.mem_Icc]
        have hvRange := hURange v hv
        constructor <;> linarith
      · dsimp only [a]
        exact norm_phaseShifted_normalized_reflected_eq sigma T v (2 ^ j) M
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_positive_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hPositive
    let a : ℕ → ℂ := normalizedTypeIReflectedCoeff sigma M
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      exact norm_normalizedTypeIReflectedCoeff_le_one (by linarith)
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨v, hURange v hv, ?_⟩
      rfl
-/

/-! ## Dual-scale arithmetic -/

/-- If `T = Q^τ`, the reflected length `T/Q` has logarithmic scale
`τ / (τ - 1)`.  This is the exact scale change used by the B-process;
in particular, no direct MHH exponent at the original medium scale is
silently substituted for the reflected one. -/
theorem reflected_logarithmic_scale_identity
    {T Q M τ : ℝ} (hT : 0 < T) (hQ : 1 < Q)
    (hτ : Q ^ τ = T) (hM : M = T / Q) :
    Real.log T / Real.log M = τ / (τ - 1) := by
  have hlogQ : Real.log Q ≠ 0 := (Real.log_pos hQ).ne'
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hlogT : Real.log T = τ * Real.log Q := by
    rw [← hτ, Real.log_rpow hQpos]
  have hlogM : Real.log M = (τ - 1) * Real.log Q := by
    rw [hM, Real.log_div hT.ne' hQpos.ne', hlogT]
    ring
  rw [hlogT, hlogM]
  field_simp [hlogQ]

/-- A medium original scale below two reflects to a genuine zeta-polynomial
scale at least two.  This is the branch point used before applying the
certificate's zeta-window alternative or finite powering. -/
theorem two_le_reflected_scale_of_medium
    {τ : ℝ} (hτOne : 1 < τ) (hτTwo : τ ≤ 2) :
    2 ≤ τ / (τ - 1) := by
  rw [le_div_iff₀ (by linarith : 0 < τ - 1)]
  linarith

/-- The exact alternatives for a reflected medium scale.  Once the
original scale is below two, the B-process scale is at least two.  It is
therefore either in the raised-scale powering range or in the certificate's
exceptional zeta window.  In the latter case the certificate says that the
window is empty or lies in the proved Weyl range.  This lemma is deliberately
stated without any polynomial: it is the real-arithmetic routing bridge used
after the exact Poisson/Mellin extraction. -/
theorem reflected_medium_scale_power_or_weyl
    {σ τ₀ τ : ℝ} (hcert : EndpointScaleCertificate σ τ₀)
    (hτOne : 1 < τ) (hτTwo : τ ≤ 2) :
    4 * τ₀ / 3 ≤ τ / (τ - 1) ∨
      False ∨ τ / (τ - 1) < 6 * σ - 3 := by
  let θ := τ / (τ - 1)
  have hθTwo : 2 ≤ θ := by
    simpa only [θ] using two_le_reflected_scale_of_medium hτOne hτTwo
  by_cases hRaised : 4 * τ₀ / 3 ≤ θ
  · exact Or.inl hRaised
  · exact Or.inr (hcert.zeta_window θ hθTwo (lt_of_not_ge hRaised))

/-- The small expansion used in the finite Poisson cutoff cannot create an
uncontrolled gap between the reflected scale and the endpoint alternatives.
If an actual dyadic block has scale at least `1 / (1/2+d)`, then it is either
in the exact powered range or in the Weyl range with the explicit `4d`
slack paid later from the epsilon budget.  The two numerical alternatives
in `EndpointScaleCertificate` are handled separately; this is the finite
boundary calculation which replaces an invalid identification of the
expanded cutoff with `T/Q`. -/
theorem reflected_actual_scale_power_or_weyl_with_slack
    {σ τ₀ τ d : ℝ}
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 < d) (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (hτLower : 1 / (1 / 2 + d) ≤ τ) :
    4 * τ₀ / 3 ≤ τ ∨ τ < 6 * σ - 3 + 4 * d := by
  by_cases hRaised : 4 * τ₀ / 3 ≤ τ
  · exact Or.inl hRaised
  right
  have hτUpper : τ < 4 * τ₀ / 3 := lt_of_not_ge hRaised
  have hReciprocal : 2 - 4 * d < 1 / (1 / 2 + d) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1 / 2 + d)]
    nlinarith [sq_pos_of_pos hd]
  have hNearTwo : 2 - 4 * d < τ := hReciprocal.trans_le hτLower
  rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
  · have hUpperI : τ < 4 * (2 - σ) / 3 := by
      exact hτUpper.trans_le (by gcongr)
    have hGapPos : 0 < σ - 1 / 2 := by linarith
    have hScaled : 1000 * d ≤ σ - 1 / 2 := by
      nlinarith
    nlinarith
  · have hUpperH : τ < 4 * (3 * σ - 1) / 3 := by
      exact hτUpper.trans_le (by gcongr)
    nlinarith

/-- Power selection for the finite `4d` transition strip.  It is applied to
the augmented scale `τ+4d`; the selected power is uniformly bounded, its
augmented scale lies in the exact endpoint window, and its actual scale is
at most `4d` below that window. -/
theorem exists_bounded_positive_power_scale_reduction_with_slack
    {τ₀ τ U d : ℝ} (hτ₀ : 0 < τ₀) (hd : 0 ≤ d)
    (hNear : 4 * τ₀ / 3 - 4 * d ≤ τ)
    (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧ k ≤ ⌈3 * (U + 4 * d) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + 4 * d) / k ∧
      (τ + 4 * d) / k ≤ τ₀ ∧
      τ / k ≤ (τ + 4 * d) / k ∧
      (τ + 4 * d) / k - τ / k ≤ 4 * d := by
  have hRaised : 4 * τ₀ / 3 ≤ τ + 4 * d := by linarith
  have hUpper : τ + 4 * d ≤ U + 4 * d := by linarith
  obtain ⟨k, hk, hkB, hkLower, hkUpper⟩ :=
    exists_bounded_positive_power_scale_reduction hτ₀ hRaised hUpper
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨k, hk, hkB, hkLower, hkUpper, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hkPos.le
  · rw [← sub_div]
    have hFour : 4 * d / (k : ℝ) ≤ 4 * d := by
      exact div_le_self (by positivity) hkReal
    calc
      (τ + 4 * d - τ) / (k : ℝ) = 4 * d / (k : ℝ) := by ring
      _ ≤ 4 * d := hFour

/-- The transition width used in the reflected endpoint argument.  The
factor `σ - 1/2` is the exact gap that degenerates at the left edge of the
critical strip; scaling by its reciprocal gives the Weyl branch a uniform
positive exponent margin.  The dedicated term in
`classicalEndpointLossParameter` makes this width epsilon-small. -/
noncomputable def reflectedEndpointScaleSlack (σ d : ℝ) : ℝ :=
  100 * d / (σ - 1 / 2)

theorem reflectedEndpointScaleSlack_pos
    {σ d : ℝ} (hσ : 1 / 2 < σ) (hd : 0 < d) :
    0 < reflectedEndpointScaleSlack σ d := by
  unfold reflectedEndpointScaleSlack
  positivity

theorem four_mul_le_reflectedEndpointScaleSlack
    {σ d : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1) (hd : 0 ≤ d) :
    4 * d ≤ reflectedEndpointScaleSlack σ d := by
  unfold reflectedEndpointScaleSlack
  by_cases hdz : d = 0
  · simp [hdz]
  · have hdPos : 0 < d := lt_of_le_of_ne hd (Ne.symm hdz)
    have hgap : 0 < σ - 1 / 2 := by linarith
    rw [le_div_iff₀ hgap]
    nlinarith

/-- Both critical-strip side-gap terms in the global loss parameter make the
reflected transition width smaller than one sixth of the endpoint scale. -/
theorem reflectedEndpointScaleSlack_le_tau0_sixth
    {σ τ₀ d : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (hdUpperGap : d ≤ (1 - σ) / 1000) :
    reflectedEndpointScaleSlack σ d ≤ τ₀ / 6 := by
  have hgap : 0 < σ - 1 / 2 := by linarith
  have hDensity : 3 * (1 - σ) ≤ τ₀ := by
    nlinarith [hcert.density_base_le_tau0]
  have hSlackCore : reflectedEndpointScaleSlack σ d ≤
      (2 / 5 : ℝ) * (1 - σ) := by
    unfold reflectedEndpointScaleSlack
    by_cases hmid : σ ≤ 3 / 4
    · have hOneSigma : 1 / 4 ≤ 1 - σ := by linarith
      have hdScaled : 100 * d ≤ (σ - 1 / 2) / 10 := by nlinarith
      rw [div_le_iff₀ hgap]
      have hgapUpper : σ - 1 / 2 ≤ 1 / 4 := by linarith
      nlinarith [mul_pos hgap (sub_pos.mpr hσUpper)]
    · have hgapQuarter : 1 / 4 ≤ σ - 1 / 2 := by linarith
      have hdScaled : 100 * d ≤ (1 - σ) / 10 := by nlinarith
      rw [div_le_iff₀ hgap]
      nlinarith
  nlinarith

/-- Natural power selection after augmenting an actual reflected scale by an
arbitrary nonnegative transition width.  The returned `k` is the literal
natural exponent used by finite Dirichlet-polynomial powering. -/
theorem exists_bounded_positive_power_scale_reduction_with_gap
    {τ₀ τ U s : ℝ} (hτ₀ : 0 < τ₀) (hs : 0 ≤ s)
    (hNear : 4 * τ₀ / 3 - s ≤ τ)
    (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧ k ≤ ⌈3 * (U + s) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + s) / k ∧
      (τ + s) / k ≤ τ₀ ∧
      τ / k ≤ (τ + s) / k ∧
      (τ + s) / k - τ / k ≤ s := by
  have hRaised : 4 * τ₀ / 3 ≤ τ + s := by linarith
  have hUpper : τ + s ≤ U + s := by linarith
  obtain ⟨k, hk, hkB, hkLower, hkUpper⟩ :=
    exists_bounded_positive_power_scale_reduction hτ₀ hRaised hUpper
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨k, hk, hkB, hkLower, hkUpper, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hkPos.le
  · rw [← sub_div]
    have hGap : s / (k : ℝ) ≤ s := div_le_self hs hkReal
    calc
      (τ + s - τ) / (k : ℝ) = s / (k : ℝ) := by ring
      _ ≤ s := hGap

/-- Endpoint form of the preceding selector.  It also records the lower
bound for the actual powered scale and pays exactly for replacing that scale
by the augmented one. -/
theorem exists_bounded_positive_power_augmented_endpoint_with_gap
    {σ τ₀ τ U s d : ℝ}
    (_hσUpper : σ < 1) (hcert : EndpointScaleCertificate σ τ₀)
    (hs : 0 ≤ s) (_hdUpper : d ≤ (1 - σ) / 1000)
    (hSmall : s ≤ τ₀ / 6)
    (hNear : 4 * τ₀ / 3 - s ≤ τ) (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧
      k ≤ ⌈3 * (U + s) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + s) / k ∧
      (τ + s) / k ≤ τ₀ ∧
      τ / k ≤ (τ + s) / k ∧
      τ₀ / 2 ≤ τ / k ∧
      (3 * (1 - σ) / τ₀) *
          ((τ + s) / k - τ / k) ≤
        (2 * s / τ₀) * (τ / k) := by
  obtain ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hkGap⟩ :=
    exists_bounded_positive_power_scale_reduction_with_gap
      hcert.tau0_pos hs hNear hτUpper
  have hTauDensity : 3 * (1 - σ) ≤ τ₀ := by
    nlinarith [hcert.density_base_le_tau0]
  have hActualLower : τ₀ / 2 ≤ τ / k := by
    have hGapAt : (τ + s) / k - s ≤ τ / k := by linarith
    have hCore : τ₀ / 2 ≤ (τ + s) / k - s := by
      nlinarith [hkLower]
    exact hCore.trans hGapAt
  have hTargetLeOne : 3 * (1 - σ) / τ₀ ≤ 1 := by
    rw [div_le_one hcert.tau0_pos]
    exact hTauDensity
  have hGapNonneg : 0 ≤ (τ + s) / k - τ / k :=
    sub_nonneg.mpr hkActual
  refine ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hActualLower, ?_⟩
  calc
    (3 * (1 - σ) / τ₀) * ((τ + s) / k - τ / k) ≤ 1 * s := by
      gcongr
    _ ≤ (2 * s / τ₀) * (τ / k) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hcert.tau0_pos).2
      have hActualNonneg : 0 ≤ τ / (k : ℝ) :=
        (div_nonneg hcert.tau0_pos.le (by norm_num)).trans hActualLower
      nlinarith [mul_nonneg hs hActualNonneg]

/-- The augmented-scale power selector already supplies the exact exponent
budget required by the endpoint conversion.  The lower density constraint
in the certificate and the explicit `d ≤ (1-σ)/1000` bound keep the actual
powered scale uniformly positive after the `4d` correction. -/
theorem exists_bounded_positive_power_augmented_endpoint
    {σ τ₀ τ U d : ℝ}
    (hσUpper : σ < 1) (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 ≤ d) (hdUpper : d ≤ (1 - σ) / 1000)
    (hNear : 4 * τ₀ / 3 - 4 * d ≤ τ) (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧
      k ≤ ⌈3 * (U + 4 * d) / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ (τ + 4 * d) / k ∧
      (τ + 4 * d) / k ≤ τ₀ ∧
      τ / k ≤ (τ + 4 * d) / k ∧
      τ₀ / 2 ≤ τ / k ∧
      (3 * (1 - σ) / τ₀) *
          ((τ + 4 * d) / k - τ / k) ≤
        (8 * d / τ₀) * (τ / k) := by
  obtain ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hkGap⟩ :=
    exists_bounded_positive_power_scale_reduction_with_slack
      hcert.tau0_pos hd hNear hτUpper
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  have hTauDensity : 3 * (1 - σ) ≤ τ₀ := by
    nlinarith [hcert.density_base_le_tau0]
  have hdTau : 4 * d ≤ τ₀ / 750 := by
    nlinarith
  have hActualLower : τ₀ / 2 ≤ τ / k := by
    have hGapAt : (τ + 4 * d) / k - 4 * d ≤ τ / k := by linarith
    have hCore : τ₀ / 2 ≤ (τ + 4 * d) / k - 4 * d := by
      nlinarith [hkLower]
    exact hCore.trans hGapAt
  have hTargetLeOne : 3 * (1 - σ) / τ₀ ≤ 1 := by
    rw [div_le_one hcert.tau0_pos]
    exact hTauDensity
  have hGapNonneg : 0 ≤ (τ + 4 * d) / k - τ / k := by
    exact sub_nonneg.mpr hkActual
  refine ⟨k, hk, hkB, hkLower, hkUpper, hkActual, hActualLower, ?_⟩
  calc
    (3 * (1 - σ) / τ₀) * ((τ + 4 * d) / k - τ / k) ≤
        1 * (4 * d) := by gcongr
    _ ≤ (8 * d / τ₀) * (τ / k) := by
      have hτ₀Pos := hcert.tau0_pos
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hτ₀Pos).2
      have hActualNonneg : 0 ≤ τ / (k : ℝ) :=
        (by positivity : 0 ≤ τ₀ / 2).trans hActualLower
      nlinarith [mul_nonneg hd hActualNonneg]

/-- The single endpoint loss parameter controls every real-power loss that
arises after reflected finite powering.  The natural ceiling is kept
literal: its contribution is bounded from `Nat.ceil_lt_add_one`, while the
factor `1 / (sigma - 1/2)` is paid for by the dedicated half-line-gap term
in `classicalEndpointLossParameter`. -/
theorem reflected_total_power_budget_le
    {sigma tau0 eta d : ℝ}
    (hsigma : 1 / 2 < sigma) (htau0 : 0 < tau0) (heta : 0 < eta)
    (hd : 0 < d) (hdOne : d ≤ 1)
    (hdEta : d ≤ eta / 1000)
    (hdEtaTau : d ≤ eta * tau0 / 1000)
    (hdReflected : d ≤ eta * tau0 * (sigma - 1 / 2) / 1000000) :
    let g := (sigma - 1 / 2) / 2
    let U := 2 / g
    let B := ⌈3 * (U + 4 * d) / (2 * tau0)⌉₊
    24 * d * (B : ℝ) + 8 * d / tau0 + 6 * d ≤ eta / 4 := by
  dsimp only
  let gap : ℝ := sigma - 1 / 2
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  let U : ℝ := 4 / gap
  have hU : 0 < U := by dsimp only [U]; positivity
  let x : ℝ := 3 * (U + 4 * d) / (2 * tau0)
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  let B : ℕ := ⌈x⌉₊
  have hB : (B : ℝ) < x + 1 := by
    simpa only [B] using Nat.ceil_lt_add_one hx
  have hdOverTau : d / tau0 ≤ eta / 1000 := by
    rw [div_le_iff₀ htau0]
    nlinarith
  have hdUOverTau : d * U / tau0 ≤ 4 * eta / 1000000 := by
    have hscaled : d / (tau0 * gap) ≤ eta / 1000000 := by
      rw [div_le_iff₀ (mul_pos htau0 hgap)]
      have hrewrite : eta / 1000000 * (tau0 * gap) =
          eta * tau0 * gap / 1000000 := by ring
      rw [hrewrite]
      simpa only [gap] using hdReflected
    dsimp only [U]
    calc
      d * (4 / gap) / tau0 = 4 * (d / (tau0 * gap)) := by
        field_simp [htau0.ne', hgap.ne']
      _ ≤ 4 * (eta / 1000000) := by gcongr
      _ = 4 * eta / 1000000 := by ring
  have hdSqOverTau : d ^ 2 / tau0 ≤ eta / 1000 := by
    calc
      d ^ 2 / tau0 = d * (d / tau0) := by ring
      _ ≤ 1 * (eta / 1000) := by
        exact mul_le_mul hdOne hdOverTau (by positivity) (by positivity)
      _ = eta / 1000 := by ring
  have hdB : d * (B : ℝ) <
      (3 / 2 : ℝ) * (d * U / tau0) +
        6 * (d ^ 2 / tau0) + d := by
    have hmul := mul_lt_mul_of_pos_left hB hd
    dsimp only [x] at hmul
    have hrewrite : d * (3 * (U + 4 * d) / (2 * tau0) + 1) =
        (3 / 2 : ℝ) * (d * U / tau0) +
          6 * (d ^ 2 / tau0) + d := by
      field_simp [htau0.ne']
      ring
    rwa [hrewrite] at hmul
  have hdB' : d * (B : ℝ) ≤ 8 * eta / 1000 := by
    have hEtaNonneg : 0 ≤ eta := heta.le
    nlinarith [hdUOverTau, hdSqOverTau, hdEta]
  have hFinal :
      24 * d * (B : ℝ) + 8 * d / tau0 + 6 * d ≤ eta / 4 := by
    have hEight : 8 * d / tau0 ≤ 8 * (eta / 1000) := by
      calc
        8 * d / tau0 = 8 * (d / tau0) := by ring
        _ ≤ 8 * (eta / 1000) := by gcongr
    nlinarith [hdB', hEight, hdEta]
  have hUrewrite : 2 / ((sigma - 1 / 2) / 2) = U := by
    dsimp only [U, gap]
    field_simp [show sigma - 1 / 2 ≠ 0 by linarith]
    norm_num
  rw [hUrewrite]
  simpa only [B, x] using hFinal

/-- The dedicated half-line-gap budget controls both the enlarged natural
power ceiling and the endpoint-exponent displacement caused by
`reflectedEndpointScaleSlack`. -/
theorem reflected_total_power_budget_with_gap_le
    {sigma tau0 eta d : ℝ}
    (hsigma : 1 / 2 < sigma) (_hsigmaUpper : sigma < 1)
    (htau0 : 0 < tau0) (_heta : 0 < eta)
    (hd : 0 < d) (hdOne : d ≤ 1)
    (hdEta : d ≤ eta / 1000)
    (hdReflected : d ≤ eta * tau0 * (sigma - 1 / 2) / 1000000) :
    let s := reflectedEndpointScaleSlack sigma d
    let g := (sigma - 1 / 2) / 2
    let U := 2 / g
    let B := ⌈3 * (U + s) / (2 * tau0)⌉₊
    24 * d * (B : ℝ) + 2 * s / tau0 + 6 * d ≤ eta / 4 := by
  dsimp only
  let gap : ℝ := sigma - 1 / 2
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  let s : ℝ := 100 * d / gap
  have hs : 0 < s := by dsimp only [s]; positivity
  let U : ℝ := 4 / gap
  have hU : 0 < U := by dsimp only [U]; positivity
  let x : ℝ := 3 * (U + s) / (2 * tau0)
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  let B : ℕ := ⌈x⌉₊
  have hB : (B : ℝ) < x + 1 := by
    simpa only [B] using Nat.ceil_lt_add_one hx
  have hdGapTau : d / (tau0 * gap) ≤ eta / 1000000 := by
    rw [div_le_iff₀ (mul_pos htau0 hgap)]
    have hrewrite : eta / 1000000 * (tau0 * gap) =
        eta * tau0 * gap / 1000000 := by ring
    rw [hrewrite]
    simpa only [gap] using hdReflected
  have hsTau : s / tau0 ≤ eta / 10000 := by
    dsimp only [s]
    calc
      (100 * d / gap) / tau0 = 100 * (d / (tau0 * gap)) := by
        field_simp [htau0.ne', hgap.ne']
      _ ≤ 100 * (eta / 1000000) := by gcongr
      _ = eta / 10000 := by ring
  have hdUTau : d * U / tau0 ≤ 4 * eta / 1000000 := by
    dsimp only [U]
    calc
      d * (4 / gap) / tau0 = 4 * (d / (tau0 * gap)) := by
        field_simp [htau0.ne', hgap.ne']
      _ ≤ 4 * (eta / 1000000) := by gcongr
      _ = 4 * eta / 1000000 := by ring
  have hdSTau : d * s / tau0 ≤ eta / 10000 := by
    calc
      d * s / tau0 = d * (s / tau0) := by ring
      _ ≤ 1 * (eta / 10000) := by
        exact mul_le_mul hdOne hsTau (div_nonneg hs.le htau0.le) (by norm_num)
      _ = eta / 10000 := by ring
  have hdB : d * (B : ℝ) <
      (3 / 2 : ℝ) * (d * U / tau0) +
        (3 / 2 : ℝ) * (d * s / tau0) + d := by
    have hmul := mul_lt_mul_of_pos_left hB hd
    dsimp only [x] at hmul
    have hrewrite : d * (3 * (U + s) / (2 * tau0) + 1) =
        (3 / 2 : ℝ) * (d * U / tau0) +
          (3 / 2 : ℝ) * (d * s / tau0) + d := by
      field_simp [htau0.ne']
    rwa [hrewrite] at hmul
  have hdB' : d * (B : ℝ) ≤ eta / 100 := by
    nlinarith [hdUTau, hdSTau, hdEta]
  have hFinal :
      24 * d * (B : ℝ) + 2 * s / tau0 + 6 * d ≤ eta / 4 := by
    have hTwo : 2 * s / tau0 ≤ 2 * (eta / 10000) := by
      calc
        2 * s / tau0 = 2 * (s / tau0) := by ring
        _ ≤ 2 * (eta / 10000) := by gcongr
    nlinarith [hdB', hTwo, hdEta]
  have hSrewrite : reflectedEndpointScaleSlack sigma d = s := by
    rfl
  have hUrewrite : 2 / ((sigma - 1 / 2) / 2) = U := by
    dsimp only [U, gap]
    field_simp [show sigma - 1 / 2 ≠ 0 by linarith]
    norm_num
  rw [hSrewrite, hUrewrite]
  simpa only [B, x] using hFinal

/-- A dyadic block selected from the expanded reflected prefix retains a
literal lower bound for its logarithmic height scale.  Floors are kept in
the hypothesis through the natural upper bound on `M`; no equality with the
ideal dual length is asserted. -/
theorem reflected_dyadic_scale_lower_of_expanded_cutoff
    {T τ d : ℝ} {Q P M : ℕ}
    (hT : 1 < T) (hQ : 1 < Q) (hP : 1 < P)
    (hτ : 1 < τ) (hτTwo : τ < 2)
    (hd : 0 ≤ d) (hScale : (Q : ℝ) ^ τ = T)
    (hPM : P ≤ M) (hM : (M : ℝ) ≤ T ^ (1 + d) / Q) :
    1 / (1 / 2 + d) ≤ typeILogarithmicScale T P := by
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := hT.le
  have hQReal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hSqrtQ : T ^ (1 / 2 : ℝ) ≤ (Q : ℝ) := by
    rw [← hScale, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Q)]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      hQReal.le (by nlinarith : τ * (1 / 2 : ℝ) ≤ 1)
  have hSplit : T ^ (1 + d) = T ^ (1 / 2 + d) * T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hMUpper : (M : ℝ) ≤ T ^ (1 / 2 + d) := by
    calc
      (M : ℝ) ≤ T ^ (1 + d) / Q := hM
      _ ≤ T ^ (1 + d) / T ^ (1 / 2 : ℝ) := by
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hTPos.le _)
          (Real.rpow_pos_of_pos hTPos _)
          hSqrtQ
      _ = T ^ (1 / 2 + d) := by
        rw [hSplit]
        field_simp [(Real.rpow_pos_of_pos hTPos (1 / 2 : ℝ)).ne']
  have hPUpper : (P : ℝ) ≤ T ^ (1 / 2 + d) := by
    exact (by exact_mod_cast hPM : (P : ℝ) ≤ M) |>.trans hMUpper
  have ha : 0 < 1 / 2 + d := by linarith
  have hInv : 0 ≤ 1 / (1 / 2 + d) := by positivity
  have hRaised := Real.rpow_le_rpow (Nat.cast_nonneg P) hPUpper hInv
  have hCancel : (T ^ (1 / 2 + d)) ^ (1 / (1 / 2 + d)) = T := by
    rw [← Real.rpow_mul hTPos.le]
    field_simp [ha.ne']
    exact Real.rpow_one T
  apply (Real.le_logb_iff_rpow_le (by exact_mod_cast hP) hTPos).mpr
  exact hRaised.trans_eq hCancel

/-- If the exceptional zeta window is nonempty, its entire upper endpoint
lies strictly below the Weyl threshold.  This strengthens the pointwise
strict inequality stored in `EndpointScaleCertificate` to the uniform gap
needed when an epsilon-power estimate is assembled. -/
theorem endpoint_zeta_window_upper_lt_weyl
    {σ τ₀ : ℝ} (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hWindow : 2 < 4 * τ₀ / 3) :
    4 * τ₀ / 3 < 6 * σ - 3 := by
  have hAtTwo := hcert.zeta_window 2 (by norm_num) hWindow
  have hSigma : 5 / 6 < σ := by
    rcases hAtTwo with hFalse | hTwo
    · exact False.elim hFalse
    · linarith
  rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
  · have : 4 * τ₀ / 3 < 2 := by
      calc
        4 * τ₀ / 3 ≤ 4 * (2 - σ) / 3 := by gcongr
        _ < 2 := by linarith
    linarith
  · calc
      4 * τ₀ / 3 ≤ 4 * (3 * σ - 1) / 3 := by gcongr
      _ < 6 * σ - 3 := by linarith

/-- Exhaustive version with a strict Weyl margin.  The `4d` strip directly
below the powered boundary is deliberately retained for a slackened powered
MHH argument.  Outside that strip, the actual dyadic scale lies at least
`4d` below the Weyl threshold. -/
theorem reflected_actual_scale_powered_slack_or_weyl_margin
    {σ τ₀ τ d : ℝ}
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 < d)
    (hτLower : 1 / (1 / 2 + d) ≤ τ) :
    4 * τ₀ / 3 - 4 * d ≤ τ ∨
      τ < 6 * σ - 3 - 4 * d := by
  by_cases hNear : 4 * τ₀ / 3 - 4 * d ≤ τ
  · exact Or.inl hNear
  right
  have hBelow : τ + 4 * d < 4 * τ₀ / 3 := by linarith
  have hReciprocal : 2 - 4 * d < 1 / (1 / 2 + d) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1 / 2 + d)]
    nlinarith [sq_pos_of_pos hd]
  have hNearTwo : 2 - 4 * d < τ := hReciprocal.trans_le hτLower
  have hWindow : 2 < 4 * τ₀ / 3 := by linarith
  have hWeyl := endpoint_zeta_window_upper_lt_weyl hσUpper hcert hWindow
  linarith

/-- Exhaustive reflected split with the gap-scaled transition width.  The
strict complementary alternative now retains a margin large enough to pay
all floored-cutoff and finite-power losses uniformly as `σ ↓ 5/6`. -/
theorem reflected_actual_scale_powered_gap_or_weyl_margin
    {σ τ₀ τ d : ℝ}
    (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 < d)
    (hτLower : 1 / (1 / 2 + d) ≤ τ) :
    let s := reflectedEndpointScaleSlack σ d
    4 * τ₀ / 3 - s ≤ τ ∨ τ < 6 * σ - 3 - s := by
  dsimp only
  let s := reflectedEndpointScaleSlack σ d
  have hs : 0 < s := reflectedEndpointScaleSlack_pos hσ hd
  have hFour : 4 * d ≤ s :=
    four_mul_le_reflectedEndpointScaleSlack hσ hσUpper hd.le
  by_cases hNear : 4 * τ₀ / 3 - s ≤ τ
  · exact Or.inl hNear
  right
  have hBelow : τ + s < 4 * τ₀ / 3 := by linarith
  have hReciprocal : 2 - 4 * d < 1 / (1 / 2 + d) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1 / 2 + d)]
    nlinarith [sq_pos_of_pos hd]
  have hNearTwo : 2 - 4 * d < τ := hReciprocal.trans_le hτLower
  have hWindow : 2 < 4 * τ₀ / 3 := by linarith
  have hWeyl := endpoint_zeta_window_upper_lt_weyl hσUpper hcert hWindow
  linarith

/-- The numerical heart of the complementary reflected branch.  The first
inequality is the exact dual-length relation `P < M ≤ T^(1+d-1/τ)` written
in logarithmic coordinates.  Together with the gap-scaled transition it
leaves a fixed `s/24` between the reflected Weyl exponent and the literal
stationary threshold exponent. -/
theorem reflected_weyl_exponent_margin
    {σ τ θ d u s : ℝ}
    (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hd : 0 < d) (huD : u ≤ d)
    (hs : s = reflectedEndpointScaleSlack σ d)
    (hτOne : 1 < τ) (hτTwo : τ < 2)
    (hDual : 1 / θ ≤ 1 + d - 1 / τ)
    (hθLower : 1 / (1 / 2 + d) ≤ θ)
    (hFar : θ < 6 * σ - 3 - s) :
    1 / (2 * θ) + 1 / 6 + 2 * d + s / 24 ≤
      1 / 2 - u - d * σ + (σ - 1) / τ - d := by
  have hgap : 0 < σ - 1 / 2 := by linarith
  have hgapUpper : σ - 1 / 2 < 1 / 2 := by linarith
  have hτPos : 0 < τ := zero_lt_one.trans hτOne
  have hθPos : 0 < θ := by
    have hden : 0 < 1 / 2 + d := by linarith
    exact (div_pos (by norm_num) hden).trans_le hθLower
  have hReciprocal : 2 - 4 * d < 1 / (1 / 2 + d) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1 / 2 + d)]
    nlinarith [sq_pos_of_pos hd]
  have hSigmaMargin : s - 4 * d < 6 * σ - 5 := by
    linarith
  have hScaleSlack : 200 * d ≤ s := by
    subst s
    unfold reflectedEndpointScaleSlack
    rw [le_div_iff₀ hgap]
    nlinarith [mul_pos hd hgap]
  have hTauGap : (σ - 1 / 2) / 2 < (σ - 1 / 2) / τ := by
    exact div_lt_div_of_pos_left hgap hτPos hτTwo
  have hInvTheta : 1 / (2 * θ) ≤ (1 + d - 1 / τ) / 2 := by
    have := div_le_div_of_nonneg_right hDual (by norm_num : (0 : ℝ) ≤ 2)
    calc
      1 / (2 * θ) = (1 / θ) / 2 := by field_simp [hθPos.ne']
      _ ≤ (1 + d - 1 / τ) / 2 := this
  have hdSigma : d * σ < d := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hσUpper hd
  have hSourceGap : 1 / 6 + s / 12 - d / 3 < (σ - 1 / 2) / 2 := by
    linarith
  have hActualGap : 1 / 6 + s / 12 - d / 3 < (σ - 1 / 2) / τ :=
    hSourceGap.trans hTauGap
  have hLoss :
      u + d * σ + 7 * d / 2 + s / 24 ≤ s / 12 - d / 3 := by
    linarith
  have hDivIdentity :
      (σ - 1) / τ + 1 / (2 * τ) = (σ - 1 / 2) / τ := by
    field_simp [hτPos.ne']
    ring
  calc
    1 / (2 * θ) + 1 / 6 + 2 * d + s / 24 ≤
        (1 + d - 1 / τ) / 2 + 1 / 6 + 2 * d + s / 24 := by
      linarith
    _ ≤ 1 / 2 - u - d * σ + (σ - 1) / τ - d := by
      rw [show (1 + d - 1 / τ) / 2 =
        1 / 2 + d / 2 - 1 / (2 * τ) by ring]
      linarith

/-- Uniform Weyl margin for every scale in the exceptional zeta window.
The right side is positive and depends only on the fixed endpoint data,
not on the height or on the dyadic block selected later. -/
theorem endpoint_zeta_window_uniform_margin
    {σ τ₀ τ : ℝ} (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hτLower : 2 ≤ τ) (hτUpper : τ < 4 * τ₀ / 3) :
    0 < (6 * σ - 3 - 4 * τ₀ / 3) / 12 ∧
      τ / 6 + 1 / 2 - σ ≤
        -((6 * σ - 3 - 4 * τ₀ / 3) / 12) := by
  have hWindow : 2 < 4 * τ₀ / 3 := hτLower.trans_lt hτUpper
  have hGap := endpoint_zeta_window_upper_lt_weyl
    hσUpper hcert hWindow
  constructor
  · linarith
  · linarith

/-- Natural-power selection in the exact form used by both the original
Type-II branch and every raised reflected Type-I block.  In particular the
selected power is positive and the physical logarithmic scale divided by
that power belongs to `[2 * τ₀ / 3, τ₀]`; no real-valued surrogate for
the power is introduced. -/
theorem exists_endpoint_natural_power
    {τ₀ τ : ℝ} (hτ₀ : 0 < τ₀) (hRaised : 4 * τ₀ / 3 ≤ τ) :
    ∃ k : ℕ, 0 < k ∧ 2 * τ₀ / 3 ≤ τ / k ∧ τ / k ≤ τ₀ :=
  exists_positive_power_scale_reduction hτ₀ hRaised

/-! ## Dyadic realization of a selected source block -/

/-- The fixed coefficient sequence of a source-smooth Type-I block.  All
ordinate dependence remains in the ordinary Dirichlet phase. -/
noncomputable def typeISourceDirichletCoeff
    (Y A r : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  (typeISourceSmoothWeight Y A r n : ℂ) *
    (n : ℂ) ^ (-(σ : ℂ))

/-- At integer arguments the complete source weight is between zero and one.
This includes both sharp tail boundaries and is therefore valid for every
source scale, not only the interior Poisson scales. -/
theorem typeISourceSmoothWeight_nat_mem_unitInterval
    (Y A r n : ℕ) :
    0 ≤ typeISourceSmoothWeight Y A r n ∧
      typeISourceSmoothWeight Y A r n ≤ 1 := by
  rw [typeISourceSmoothWeight, typeITailBoundary_natCast]
  split_ifs
  · have hCutNonneg := typeIDyadicCutoff_nonneg
        ((n : ℝ) / (2 ^ r * Y : ℕ))
    have hCutUpper := typeIDyadicCutoff_le_one
        ((n : ℝ) / (2 ^ r * Y : ℕ))
    simpa only [one_mul] using ⟨hCutNonneg, hCutUpper⟩
  · simp

/-- A source coefficient can be nonzero only inside the fixed annulus
`(Q/2,2Q)`, where `Q = 2^r Y`.  The strict inequalities record the zeroes of
the cutoff at both endpoints. -/
theorem typeISourceSmoothWeight_support
    {Y A r n : ℕ}
    (hn : typeISourceSmoothWeight Y A r n ≠ 0) :
    (((2 ^ r * Y : ℕ) : ℝ) / 2) < n ∧
      (n : ℝ) < 2 * (2 ^ r * Y : ℕ) := by
  let Q : ℕ := 2 ^ r * Y
  have hCut : typeIDyadicCutoff ((n : ℝ) / Q) ≠ 0 := by
    intro h
    apply hn
    unfold typeISourceSmoothWeight
    rw [h, mul_zero]
  have hQ : 0 < Q := by
    by_contra hnot
    have hQZero : Q = 0 := Nat.eq_zero_of_not_pos hnot
    apply hCut
    apply typeIDyadicCutoff_eq_zero_of_le_half
    simp [hQZero]
  constructor
  · by_contra hnot
    have hnUpper : (n : ℝ) ≤ (Q : ℝ) / 2 := by
      simpa only [Q] using le_of_not_gt hnot
    have hRatio : (n : ℝ) / Q ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hQ)]
      nlinarith
    exact hCut (typeIDyadicCutoff_eq_zero_of_le_half hRatio)
  · by_contra hnot
    have hnLower : 2 * (Q : ℝ) ≤ n := by
      simpa only [Q] using le_of_not_gt hnot
    have hRatio : 2 ≤ (n : ℝ) / Q := by
      rw [le_div_iff₀ (by exact_mod_cast hQ)]
      exact hnLower
    exact hCut (typeIDyadicCutoff_eq_zero_of_two_le hRatio)

/-- Source normalization at the lower edge of its fixed annulus.  This is the
finite analogue of multiplying a smooth zeta block by `Q^σ`; the harmless
factor two makes the coefficient bound literal even at the left edge. -/
noncomputable def normalizedTypeISourceDirichletCoeff
    (Y A r : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  ((((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ : ℝ) : ℂ)) *
    typeISourceDirichletCoeff Y A r σ n

/-- The normalized coefficients of the actual source-smooth block are bounded
by one on the entire natural line. -/
theorem norm_normalizedTypeISourceDirichletCoeff_le_one
    (Y A r : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∀ n : ℕ, ‖normalizedTypeISourceDirichletCoeff Y A r σ n‖ ≤ 1 := by
  intro n
  by_cases hw : typeISourceSmoothWeight Y A r n = 0
  · simp [normalizedTypeISourceDirichletCoeff, typeISourceDirichletCoeff, hw]
  · have hn := typeISourceSmoothWeight_support hw
    have hnPos : 0 < n := by exact_mod_cast (lt_of_le_of_lt
      (by positivity : (0 : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2)) hn.1)
    have hWeight := typeISourceSmoothWeight_nat_mem_unitInterval Y A r n
    rw [normalizedTypeISourceDirichletCoeff, typeISourceDirichletCoeff,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hWeight.1,
      Complex.norm_natCast_cpow_of_pos hnPos]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.rpow_neg (by exact_mod_cast hnPos.le), ← div_eq_mul_inv]
    have hBaseNonneg : 0 ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) := by positivity
    have hnNonneg : (0 : ℝ) ≤ n := by exact_mod_cast hnPos.le
    have hRearrange :
        ((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) *
            (typeISourceSmoothWeight Y A r n / (n : ℝ) ^ σ) =
          typeISourceSmoothWeight Y A r n *
            (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) / (n : ℝ) ^ σ) := by
      ring
    rw [hRearrange]
    rw [← Real.div_rpow hBaseNonneg hnNonneg]
    have hRatio : (((2 ^ r * Y : ℕ) : ℝ) / 2) / n ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hnPos)]
      exact hn.1.le
    calc
      typeISourceSmoothWeight Y A r n *
          ((((2 ^ r * Y : ℕ) : ℝ) / 2) / n) ^ σ ≤
        1 * 1 := by
          exact mul_le_mul hWeight.2
            (Real.rpow_le_one (by positivity) hRatio hσ)
            (Real.rpow_nonneg (by positivity) _) zero_le_one
      _ = 1 := by ring

/-- A source-smooth block is exactly one finite wide Dirichlet polynomial.
The two apparent endpoint discrepancies are genuine zero terms: the left
endpoint is killed by `typeITailBoundary`, and so is `A + 1`. -/
theorem typeISourceSmoothBlock_eq_wideDirichletPoly
    (Y A r : ℕ) (σ t : ℝ) (hY : 1 ≤ Y) :
    typeISourceSmoothBlock Y A r σ t =
      wideDirichletPoly 1 (Nat.clog 2 (A + 1))
        (typeISourceDirichletCoeff Y A r σ) t := by
  classical
  let k := Nat.clog 2 (A + 1)
  let term : ℕ → ℂ := fun n =>
    typeISourceDirichletCoeff Y A r σ n *
      (n : ℂ) ^ (-(t : ℂ) * I)
  have hSmall : Finset.Ioc 1 (A + 1) ⊆ Finset.Icc 1 (A + 1) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le,
      (Finset.mem_Ioc.mp hn).2⟩
  have hLeftZero : ∀ n ∈ Finset.Icc 1 (A + 1), n ∉ Finset.Ioc 1 (A + 1) →
      term n = 0 := by
    intro n hn hnSmall
    have hnOne : n = 1 := by
      have hnData := Finset.mem_Icc.mp hn
      simp only [Finset.mem_Ioc, not_and_or] at hnSmall
      omega
    subst n
    have hnotTail : 1 ∉ Finset.Ioc Y A := by
      simp only [Finset.mem_Ioc, not_and_or]
      exact Or.inl (by omega)
    simp only [term, typeISourceDirichletCoeff, typeISourceSmoothWeight,
      typeITailBoundary_natCast, ite_eq_right hnotTail, Nat.cast_one, zero_mul,
      Complex.ofReal_zero]
  have hSource :
      (∑ n ∈ Finset.Icc 1 (A + 1), term n) =
        ∑ n ∈ Finset.Ioc 1 (A + 1), term n := by
    symm
    exact Finset.sum_subset hSmall hLeftZero
  have hCover : A + 1 ≤ 2 ^ k := by
    dsimp only [k]
    exact Nat.le_pow_clog (by omega) (A + 1)
  have hTailSubset : Finset.Ioc 1 (A + 1) ⊆ Finset.Ioc 1 (2 ^ k) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans hCover⟩
  have hRightZero : ∀ n ∈ Finset.Ioc 1 (2 ^ k),
      n ∉ Finset.Ioc 1 (A + 1) → term n = 0 := by
    intro n hn hnSmall
    have hnAbove : A + 1 < n := by
      have hnData := Finset.mem_Ioc.mp hn
      simp only [Finset.mem_Ioc, not_and_or] at hnSmall
      omega
    have hnotTail : n ∉ Finset.Ioc Y A := by
      simp only [Finset.mem_Ioc, not_and_or]
      exact Or.inr (by omega)
    simp only [term, typeISourceDirichletCoeff, typeISourceSmoothWeight,
      typeITailBoundary_natCast, ite_eq_right hnotTail, zero_mul,
      Complex.ofReal_zero]
  have hWide :
      (∑ n ∈ Finset.Ioc 1 (2 ^ k), term n) =
        ∑ n ∈ Finset.Ioc 1 (A + 1), term n := by
    symm
    exact Finset.sum_subset hTailSubset hRightZero
  unfold typeISourceSmoothBlock wideDirichletPoly
  simp only [mul_one]
  change (∑ n ∈ Finset.Icc 1 (A + 1), term n) =
    ∑ n ∈ Finset.Ioc 1 (2 ^ k), term n
  rw [hSource, hWide]

/-- Normalizing the source coefficients scales the complete source block by
the same positive real scalar. -/
theorem wideDirichletPoly_normalizedTypeISourceDirichletCoeff
    (Y A r : ℕ) (σ t : ℝ) (hY : 1 ≤ Y) :
    wideDirichletPoly 1 (Nat.clog 2 (A + 1))
        (normalizedTypeISourceDirichletCoeff Y A r σ) t =
      (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ : ℝ) : ℂ) *
        typeISourceSmoothBlock Y A r σ t := by
  rw [typeISourceSmoothBlock_eq_wideDirichletPoly Y A r σ t hY]
  unfold wideDirichletPoly normalizedTypeISourceDirichletCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- A large actual source-smooth block yields one common nonzero dyadic
block with unit-bounded coefficients.  The selected dyadic length remains
within a factor four of the physical source scale; these inequalities are
proved from the literal support of the source coefficient rather than
postulated as a scale certificate. -/
theorem extract_normalized_source_dyadic_block
    {Y A r : ℕ} {σ V : ℝ} (W : Finset ℝ)
    (hY : 0 < Y) (hA : 1 < A) (hV : 0 < V)
    (hW : W.Nonempty) (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W, V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) :
    let k := Nat.clog 2 (A + 1)
    ∃ j ∈ Finset.range k, ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
      (∀ t ∈ W',
        (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) / k ≤
          ‖dirichletPoly (2 ^ j)
            (normalizedTypeISourceDirichletCoeff Y A r σ) t‖) ∧
      2 ^ j < 2 * (2 ^ r * Y) ∧
      2 ^ r * Y < 4 * 2 ^ j := by
  dsimp only
  let k := Nat.clog 2 (A + 1)
  have hk : 0 < k := by
    dsimp only [k]
    apply Nat.clog_pos Nat.one_lt_two
    omega
  have hQ : 0 < 2 ^ r * Y := by positivity
  have hScalePos : 0 < ((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) := by
    apply Real.rpow_pos_of_pos
    positivity
  have hWide : ∀ t ∈ W,
      ((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V ≤
        ‖wideDirichletPoly 1 k
          (normalizedTypeISourceDirichletCoeff Y A r σ) t‖ := by
    intro t ht
    rw [wideDirichletPoly_normalizedTypeISourceDirichletCoeff
      Y A r σ t hY]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hScalePos]
    exact mul_le_mul_of_nonneg_left (hLarge t ht) hScalePos.le
  obtain ⟨j, hj, W', hWsub, hCard, hLarge'⟩ :=
    exists_dyadic_block_and_subset 1 k
      (normalizedTypeISourceDirichletCoeff Y A r σ) W
      (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) hk hWide
  simp only [mul_one] at hLarge'
  have hSep' : IsSeparated 1 W' := by
    intro x hx y hy hxy
    exact hSeparated x (hWsub hx) y (hWsub hy) hxy
  have hW' : W'.Nonempty := by
    by_contra hnot
    have hCardZero : W'.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hnot)
    rw [hCardZero, Nat.cast_zero, mul_zero] at hCard
    have hWCardPos : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
    linarith
  obtain ⟨t, ht⟩ := hW'
  have hThresholdPos : 0 <
      (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) / k := by
    positivity
  have hPolyNe : dirichletPoly (2 ^ j)
      (normalizedTypeISourceDirichletCoeff Y A r σ) t ≠ 0 := by
    intro hzero
    have hAt := hLarge' t ht
    rw [hzero, norm_zero] at hAt
    linarith
  unfold dirichletPoly at hPolyNe
  obtain ⟨n, hn, hnTerm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hPolyNe
  have hnCoeff : normalizedTypeISourceDirichletCoeff Y A r σ n ≠ 0 := by
    intro hzero
    apply hnTerm
    simp [hzero]
  have hnWeight : typeISourceSmoothWeight Y A r n ≠ 0 := by
    intro hzero
    apply hnCoeff
    simp [normalizedTypeISourceDirichletCoeff,
      typeISourceDirichletCoeff, hzero]
  have hnSource := typeISourceSmoothWeight_support hnWeight
  have hnDyadic := Finset.mem_Ioc.mp hn
  have hLeftReal : ((2 ^ j : ℕ) : ℝ) <
      2 * (2 ^ r * Y : ℕ) := by
    have hPn : ((2 ^ j : ℕ) : ℝ) < n := by exact_mod_cast hnDyadic.1
    exact hPn.trans hnSource.2
  have hRightReal : ((2 ^ r * Y : ℕ) : ℝ) <
      4 * (2 ^ j : ℕ) := by
    have hnUpper : (n : ℝ) ≤ 2 * (2 ^ j : ℕ) := by exact_mod_cast hnDyadic.2
    nlinarith [hnSource.1]
  refine ⟨j, hj, W', hWsub, hSep', hCard, ?_, ?_, ?_⟩
  · simpa only [k] using hLarge'
  · exact_mod_cast hLeftReal
  · exact_mod_cast hRightReal

/-- Complete direct-MHH consumer for one actual source-smooth family.  It
performs the common dyadic selection internally, preserves the source-family
cardinality, and exposes the physical/dyadic scale comparison used by the
later endpoint routing. -/
theorem source_smooth_family_direct_mhh_cardinality :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Y A r : ℕ} {σ T V : ℝ} (W : Finset ℝ),
        0 < Y → 1 < A → 0 ≤ σ → 1 ≤ T → 0 < V →
        W.Nonempty → IsSeparated 1 W → InBaseInterval (3 * T) W →
        (∀ t ∈ W, V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) →
        ∃ j ∈ Finset.range (Nat.clog 2 (A + 1)),
          ∃ W' : Finset ℝ,
            W' ⊆ W ∧ IsSeparated 1 W' ∧ InBaseInterval (3 * T) W' ∧
            (W.card : ℝ) ≤
              (Nat.clog 2 (A + 1) : ℝ) * (W'.card : ℝ) ∧
            let P := 2 ^ j
            let L := (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) /
              Nat.clog 2 (A + 1)
            (∀ t ∈ W', L ≤
              ‖dirichletPoly P
                (normalizedTypeISourceDirichletCoeff Y A r σ) t‖) ∧
            (W'.card : ℝ) ≤
              K * (1 + (((harmonic P : ℚ) : ℝ))) *
                ((P : ℝ) ^ 2 / L ^ 2 +
                  (3 * T) * min ((P : ℝ) / L ^ 2)
                    ((P : ℝ) ^ 4 / L ^ 6)) ∧
            P < 2 * (2 ^ r * Y) ∧ 2 ^ r * Y < 4 * P := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  refine ⟨K, hK, ?_⟩
  intro Y A r σ T V W hY hA hσ hT hV hW hSeparated hBase hLarge
  obtain ⟨j, hj, W', hWsub, hSep', hCard, hLarge', hPUpper, hPLower⟩ :=
    extract_normalized_source_dyadic_block W hY hA hV hW hSeparated hLarge
  let P : ℕ := 2 ^ j
  let L : ℝ := (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) /
    Nat.clog 2 (A + 1)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    have hk : 0 < Nat.clog 2 (A + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
      ‖normalizedTypeISourceDirichletCoeff Y A r σ n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r σ hσ n
  have hBase' : InBaseInterval (3 * T) W' := by
    intro t ht
    exact hBase t (hWsub ht)
  have hMHHAt := hMHH P (3 * T) L W'
    (normalizedTypeISourceDirichletCoeff Y A r σ)
    hP (by linarith) hL hCoeff hSep' hBase'
    (by simpa only [P, L] using hLarge')
  refine ⟨j, hj, W', hWsub, hSep', hBase', hCard, ?_⟩
  dsimp only
  refine ⟨by simpa only [P, L] using hLarge', ?_, hPUpper, hPLower⟩
  simpa only [P, L] using hMHHAt

/-- Powered-MHH consumer for an actual source-smooth family.  Both finite
pigeonhole losses are explicit: first the source block is localized to one
dyadic interval, then its exact natural power is localized again. -/
theorem source_smooth_family_powered_mhh_cardinality
    (B : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ {Y A r k : ℕ} {σ T V : ℝ} (W : Finset ℝ),
        0 < Y → 1 < A → 0 ≤ σ → 1 ≤ T → 0 < V →
        0 < k → k ≤ B → W.Nonempty →
        IsSeparated 1 W → InBaseInterval (3 * T) W →
        (∀ t ∈ W, V ≤ ‖typeISourceSmoothBlock Y A r σ t‖) →
        ∃ j ∈ Finset.range (Nat.clog 2 (A + 1)),
          ∃ s ∈ Finset.range k, ∃ W' : Finset ℝ,
            let P := 2 ^ j
            let Q := 2 ^ s * P ^ k
            let L := (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) /
              Nat.clog 2 (A + 1)
            let Vp := (L ^ k /
              (C * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ eta)) / k
            W' ⊆ W ∧ IsSeparated 1 W' ∧ InBaseInterval (3 * T) W' ∧
            (W.card : ℝ) ≤
              (Nat.clog 2 (A + 1) : ℝ) * k * (W'.card : ℝ) ∧
            (∀ t ∈ W', Vp ≤
              ‖dirichletPoly Q
                (normalizedFinitePoweredCoeffs P k
                  (normalizedTypeISourceDirichletCoeff Y A r σ)
                  0 C eta) t‖) ∧
            (W'.card : ℝ) ≤
              K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                ((Q : ℝ) ^ 2 / Vp ^ 2 +
                  (3 * T) * min ((Q : ℝ) / Vp ^ 2)
                    ((Q : ℝ) ^ 4 / Vp ^ 6)) ∧
            P < 2 * (2 ^ r * Y) ∧ 2 ^ r * Y < 4 * P := by
  obtain ⟨C, hC, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B eta heta
  refine ⟨C, hC, K, hK, ?_⟩
  intro Y A r k σ T V W hY hA hσ hT hV hk hkB hW hSeparated hBase hLarge
  obtain ⟨j, hj, W₀, hW₀sub, hSep₀, hCard₀, hLarge₀, hPUpper, hPLower⟩ :=
    extract_normalized_source_dyadic_block W hY hA hV hW hSeparated hLarge
  let P : ℕ := 2 ^ j
  let L : ℝ := (((((2 ^ r * Y : ℕ) : ℝ) / 2) ^ σ) * V) /
    Nat.clog 2 (A + 1)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    have hcover : 0 < Nat.clog 2 (A + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
      ‖normalizedTypeISourceDirichletCoeff Y A r σ n‖ ≤ 1 := by
    intro n _hn
    exact norm_normalizedTypeISourceDirichletCoeff_le_one Y A r σ hσ n
  have hBase₀ : InBaseInterval (3 * T) W₀ := by
    intro t ht
    exact hBase t (hW₀sub ht)
  obtain ⟨s, hs, W', hW'sub, hPowerCard, hSep', hBase', hLarge', hMHH'⟩ :=
    hPowered k P (normalizedTypeISourceDirichletCoeff Y A r σ)
      0 (3 * T) L W₀ hk hkB hP (by norm_num) (by linarith) hL
      hCoeff hSep₀ hBase₀ (by
        intro t ht
        have hPhase :
            (∑ n ∈ Finset.Ioc P (2 * P),
              normalizedTypeISourceDirichletCoeff Y A r σ n *
                (n : ℂ) ^ (-(((0 : ℝ) : ℂ) + I * (t : ℂ)))) =
              dirichletPoly P
                (normalizedTypeISourceDirichletCoeff Y A r σ) t := by
          unfold dirichletPoly
          apply Finset.sum_congr rfl
          intro n _hn
          congr 2
          norm_num
          ring
        rw [hPhase]
        simpa only [P, L] using hLarge₀ t ht)
  refine ⟨j, hj, s, hs, W', ?_⟩
  dsimp only
  refine ⟨hW'sub.trans hW₀sub, hSep', hBase', ?_, ?_, ?_,
    hPUpper, hPLower⟩
  calc
    (W.card : ℝ) ≤ (Nat.clog 2 (A + 1) : ℝ) * (W₀.card : ℝ) := hCard₀
    _ ≤ (Nat.clog 2 (A + 1) : ℝ) * (k * (W'.card : ℝ)) := by
      gcongr
    _ = (Nat.clog 2 (A + 1) : ℝ) * k * (W'.card : ℝ) := by ring
  · simpa only [P, L, Real.rpow_zero, one_mul] using hLarge'
  · simpa only [P, L, Real.rpow_zero, one_mul] using hMHH'

/-- A dyadic interval extracted within a fixed factor of a physical source
scale inherits a uniform logarithmic-scale upper bound.  The factor four is
absorbed by the elementary inequality `4P ≤ P²` once the source scale is at
least sixteen. -/
theorem extracted_source_logarithmic_scale_upper
    {T U : ℝ} {Q P : ℕ}
    (hT : 1 ≤ T) (hU : 0 < U) (hQ : 16 ≤ Q)
    (hQP : Q < 4 * P)
    (hScale : typeILogarithmicScale T Q ≤ U) :
    1 < P ∧ typeILogarithmicScale T P ≤ 2 * U := by
  have hPFour : 4 ≤ P := by omega
  have hPOne : 1 < P := by omega
  have hQOne : 1 < Q := by omega
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hPhysicalQ : T ≤ (Q : ℝ) ^ U :=
    (Real.logb_le_iff_le_rpow (by exact_mod_cast hQOne) hTPos).mp hScale
  have hQP2Nat : Q ≤ P ^ 2 := by
    calc
      Q ≤ 4 * P := hQP.le
      _ ≤ P * P := Nat.mul_le_mul_right P hPFour
      _ = P ^ 2 := by ring
  have hRaised : (Q : ℝ) ^ U ≤ ((P ^ 2 : ℕ) : ℝ) ^ U :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQP2Nat) hU.le
  have hPower : ((P ^ 2 : ℕ) : ℝ) ^ U = (P : ℝ) ^ (2 * U) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  refine ⟨hPOne, (Real.logb_le_iff_le_rpow
    (by exact_mod_cast hPOne) hTPos).mpr ?_⟩
  calc
    T ≤ (Q : ℝ) ^ U := hPhysicalQ
    _ ≤ ((P ^ 2 : ℕ) : ℝ) ^ U := hRaised
    _ = (P : ℝ) ^ (2 * U) := hPower

/-- The same extracted dyadic interval inherits half of every nonnegative
lower logarithmic-scale bound.  The exact factor-two upper comparison
`P < 2Q` is absorbed by `2Q ≤ Q²`; no asymptotic replacement of either
finite length is used. -/
theorem extracted_source_logarithmic_scale_lower
    {T L : ℝ} {Q P : ℕ}
    (hT : 0 < T) (hL : 0 ≤ L) (hQ : 4 ≤ Q)
    (hQP : Q < 4 * P) (hPQ : P < 2 * Q)
    (hScale : L ≤ typeILogarithmicScale T Q) :
    1 < P ∧ L / 2 ≤ typeILogarithmicScale T P := by
  have hPOne : 1 < P := by omega
  have hQOne : 1 < Q := by omega
  have hPhysicalQ : (Q : ℝ) ^ L ≤ T :=
    (Real.le_logb_iff_rpow_le (by exact_mod_cast hQOne) hT).mp hScale
  have hPQSquareNat : P ≤ Q ^ 2 := by
    calc
      P ≤ 2 * Q := hPQ.le
      _ ≤ Q * Q := Nat.mul_le_mul_right Q (by omega : 2 ≤ Q)
      _ = Q ^ 2 := by ring
  have hRaised : (P : ℝ) ^ (L / 2) ≤ ((Q ^ 2 : ℕ) : ℝ) ^ (L / 2) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hPQSquareNat)
      (by positivity)
  have hPower : ((Q ^ 2 : ℕ) : ℝ) ^ (L / 2) = (Q : ℝ) ^ L := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  refine ⟨hPOne, (Real.le_logb_iff_rpow_le
    (by exact_mod_cast hPOne) hT).mpr ?_⟩
  exact hRaised.trans_eq hPower |>.trans hPhysicalQ

/-- A dyadic interval within a factor two above its physical source scale
has logarithmic scale within any prescribed positive additive error once
the height is large enough.  This is the quantitative finite bridge needed
to choose the natural power from the extracted polynomial rather than from
an unrelated real surrogate. -/
theorem eventually_extracted_source_logarithmic_scale_lower_additive
    {δ U : ℝ} (hδ : 0 < δ) (hU : 0 < U) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T τ : ℝ} {Q P : ℕ}, T₀ ≤ T → 1 < Q → 1 < P →
        P < 2 * Q → τ = typeILogarithmicScale T Q →
        0 < τ → τ ≤ U →
        τ - δ ≤ typeILogarithmicScale T P := by
  let X : ℝ := U ^ 2 * Real.log 2 / δ
  let T₀ : ℝ := max 8 (Real.exp X)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T τ Q P hT hQ hP hPQ hτ hτPos hτUpper
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTExp : Real.exp X ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTOne : 1 < T := by linarith
  have hLogT : 0 < Real.log T := Real.log_pos hTOne
  have hLogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast hQ)
  have hLogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
  have hLogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hXLog : X ≤ Real.log T := by
    have hLogMono := Real.log_le_log (Real.exp_pos X) hTExp
    simpa only [Real.log_exp] using hLogMono
  have hTauLog : τ * Real.log (Q : ℝ) = Real.log T := by
    rw [hτ]
    unfold typeILogarithmicScale Real.logb
    field_simp [hLogQ.ne']
  have hLogPUpper : Real.log (P : ℝ) ≤
      Real.log 2 + Real.log (Q : ℝ) := by
    have hCast : (P : ℝ) ≤ 2 * Q := by exact_mod_cast hPQ.le
    calc
      Real.log (P : ℝ) ≤ Real.log (2 * (Q : ℝ)) :=
        Real.log_le_log (by positivity) hCast
      _ = Real.log 2 + Real.log (Q : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
  have hULog : U * Real.log 2 ≤ δ * Real.log (Q : ℝ) := by
    have hULogQ : Real.log T ≤ U * Real.log (Q : ℝ) := by
      rw [← hTauLog]
      exact mul_le_mul_of_nonneg_right hτUpper hLogQ.le
    have hCore : U ^ 2 * Real.log 2 / δ ≤
        U * Real.log (Q : ℝ) := by
      simpa only [X] using hXLog.trans hULogQ
    rw [div_le_iff₀ hδ] at hCore
    have hUPos : 0 < U := hU
    nlinarith [mul_pos hUPos hLogTwo]
  have hTauLogTwo : τ * Real.log 2 ≤ δ * Real.log (Q : ℝ) :=
    (mul_le_mul_of_nonneg_right hτUpper hLogTwo.le).trans hULog
  rw [hτ]
  unfold typeILogarithmicScale Real.logb
  rw [le_div_iff₀ hLogP]
  by_cases hNonneg : 0 ≤ Real.log T / Real.log (Q : ℝ) - δ
  · calc
      (Real.log T / Real.log (Q : ℝ) - δ) * Real.log (P : ℝ) ≤
          (Real.log T / Real.log (Q : ℝ) - δ) *
            (Real.log 2 + Real.log (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left hLogPUpper hNonneg
      _ ≤ Real.log T := by
        rw [show Real.log T / Real.log (Q : ℝ) = τ by
          rw [hτ]; rfl]
        rw [← hTauLog]
        nlinarith
  · have hNeg : Real.log T / Real.log (Q : ℝ) - δ < 0 :=
      lt_of_not_ge hNonneg
    exact (mul_neg_of_neg_of_pos hNeg hLogP).le.trans hLogT.le

/-! ## Powered reflected-family bridge -/

/-- The zero-real-part convention used by the generic powering theorem is
definitionally the ordinary Dirichlet phase after the elementary complex
ring normalization. -/
theorem sum_zero_real_part_eq_dirichletPoly
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ Finset.Ioc N (2 * N),
      a n * (n : ℂ) ^ (-(((0 : ℝ) : ℂ) + I * (t : ℂ)))) =
      dirichletPoly N a t := by
  unfold dirichletPoly
  apply Finset.sum_congr rfl
  intro n _hn
  congr 2
  norm_num
  ring

/-- A unit-coefficient dyadic polynomial cannot have norm larger than its
literal natural length.  This converts a retained reflected threshold into
a lower bound for the actual block selected by dyadic pigeonholing. -/
theorem unit_coeff_threshold_le_dyadic_length
    {N : ℕ} {V : ℝ} {W : Finset ℝ} {a : ℕ → ℂ}
    (hV : 0 ≤ V) (hW : W.Nonempty)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) :
    V ≤ (N : ℝ) := by
  have hEnergy := dyadic_energy_le_length N a ha
  have hThreshold := threshold_sq_le_length_mul_energy N V W a hV hW hLarge
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [sq_nonneg (V - (N : ℝ))]

/-- A cancellation-safe reflected family is passed through every finite
combinatorial operation needed before the endpoint exponent calculation:
sign pigeonholing, bounded-displacement reseparation, dyadic extraction,
exact natural powering, and the unrestricted Montgomery--Halasz--Huxley
estimate.  The output retains the complete cardinality loss from the input
family; in particular no displacement fibre or Poisson-sign alternative is
discarded.

The constants are uniform for all positive powers `k <= B`.  This is the
form needed after the endpoint certificate selects `k` from a physical
logarithmic scale depending on `T`. -/
theorem signed_reflected_family_powered_mhh_cardinality
    (B : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ {M k : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ),
        1 < M → 0 < k → k ≤ B → 0 ≤ sigma →
        0 ≤ H → 1 ≤ T → D + H ≤ T / 2 → 0 < S →
        IsSeparated 1 W →
        (∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D) →
        (∀ t ∈ W,
          (∃ u ∈ Set.Icc (-H) H,
            S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
              (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
          (∃ u ∈ Set.Icc (-H) H,
            S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
              (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) →
        ∃ j ∈ Finset.range (Nat.clog 2 M),
          ∃ r ∈ Finset.range k, ∃ U : Finset ℝ,
            let P := 2 ^ j
            let Q := 2 ^ r * P ^ k
            let V := ((S / Nat.clog 2 M) ^ k /
                  (C * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ eta)) / k
            IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
              (W.card : ℝ) ≤
                2 * (2 * (2 * ⌈H⌉₊ + 1)) *
                  (Nat.clog 2 M) * k * (U.card : ℝ) ∧
              (U.card : ℝ) ≤
                K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                  ((Q : ℝ) ^ 2 / V ^ 2 +
                    (3 * T) * min ((Q : ℝ) / V ^ 2)
                      ((Q : ℝ) ^ 4 / V ^ 6)) := by
  obtain ⟨C, hC, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B eta heta
  refine ⟨C, hC, K, hK, ?_⟩
  intro M k sigma T D H S W hM hk hkB hsigma hH hT hDH hS
    hSeparated hRange hEach
  have hClog : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  have hThreshold : 0 < S / Nat.clog 2 M := by positivity
  rcases select_common_signed_reflected_family W hEach with
    ⟨Wsign, hWsign, hSignCard, hNegative⟩ |
      ⟨Wsign, hWsign, hSignCard, hPositive⟩
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U₀, hSep₀, hBase₀, _hRange₀, hCard₀, hLarge₀⟩ :=
      extract_common_reflected_mhh_block Wsign hM hH
        (zero_le_one.trans hT) hDH hSepSign hRangeSign hNegative
    let P : ℕ := 2 ^ j
    have hP : 0 < P := by dsimp only [P]; positivity
    have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
        ‖phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M) n‖ ≤ 1 := by
      intro n _hn
      rw [norm_phaseShiftCoeffs]
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    obtain ⟨r, hr, U, hUsub, hPowerCard, hSepU, hBaseU,
        hLargeU, hMHHU⟩ :=
      hPowered k P
        (phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M))
        0 (3 * T) (S / Nat.clog 2 M) U₀ hk hkB hP (by norm_num)
          (by linarith) hThreshold hCoeff hSep₀ hBase₀
          (by
            intro v hv
            rw [sum_zero_real_part_eq_dirichletPoly]
            simpa only [P] using hLarge₀ v hv)
    refine ⟨j, hj, r, hr, U, ?_, ?_, ?_, ?_⟩
    · exact hSepU
    · exact hBaseU
    · calc
        (W.card : ℝ) ≤ 2 * (Wsign.card : ℝ) := by exact_mod_cast hSignCard
        _ ≤ 2 *
            ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) *
              (U₀.card : ℝ)) := by
                gcongr
                exact_mod_cast hCard₀
        _ ≤ 2 *
            ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) *
              (k * (U.card : ℝ))) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
              (Nat.clog 2 M) * k * (U.card : ℝ) := by ring
    · simpa only [P, Real.rpow_zero, one_mul] using hMHHU
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U₀, hSep₀, hBase₀, _hRange₀, hCard₀, hLarge₀⟩ :=
      extract_common_positive_reflected_mhh_block Wsign hM hH
        (zero_le_one.trans hT) hDH hSepSign hRangeSign hPositive
    let P : ℕ := 2 ^ j
    have hP : 0 < P := by dsimp only [P]; positivity
    have hCoeff : ∀ n ∈ Finset.Ioc P (2 * P),
        ‖normalizedTypeIReflectedCoeff sigma M n‖ ≤ 1 := by
      intro n _hn
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    obtain ⟨r, hr, U, hUsub, hPowerCard, hSepU, hBaseU,
        hLargeU, hMHHU⟩ :=
      hPowered k P
        (normalizedTypeIReflectedCoeff sigma M)
        0 (3 * T) (S / Nat.clog 2 M) U₀ hk hkB hP (by norm_num)
          (by linarith) hThreshold hCoeff hSep₀ hBase₀ (by
            intro v hv
            rw [sum_zero_real_part_eq_dirichletPoly]
            simpa only [P] using hLarge₀ v hv)
    refine ⟨j, hj, r, hr, U, ?_, ?_, ?_, ?_⟩
    · exact hSepU
    · exact hBaseU
    · calc
        (W.card : ℝ) ≤ 2 * (Wsign.card : ℝ) := by exact_mod_cast hSignCard
        _ ≤ 2 *
            ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) *
              (U₀.card : ℝ)) := by
                gcongr
                exact_mod_cast hCard₀
        _ ≤ 2 *
            ((2 * (2 * ⌈H⌉₊ + 1)) * (Nat.clog 2 M) *
              (k * (U.card : ℝ))) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
              (Nat.clog 2 M) * k * (U.card : ℝ) := by ring
    · simpa only [P, Real.rpow_zero, one_mul] using hMHHU

/-! ## Finite interval Abel bridges for the source boundary -/

/-- Abel summation for a nonnegative increasing weight.  Unlike the
antitone form used for `n^-sigma`, the endpoint and total variation each
cost one copy of the final weight. -/
theorem norm_weighted_sum_le_of_monotone
    (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hN : 0 < N)
    (hf : ∀ i, i < N → 0 ≤ f i)
    (hmono : ∀ i, i + 1 < N → f i ≤ f (i + 1))
    (hpartial : ∀ j, j ≤ N → ‖∑ i ∈ Finset.range j, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range N, f i • g i‖ ≤ 2 * f (N - 1) * B := by
  have hB : 0 ≤ B := by
    simpa using hpartial 0 (Nat.zero_le N)
  have hparts := Finset.sum_Ico_by_parts f g hN
  rw [Finset.range_eq_Ico]
  calc
    ‖∑ i ∈ Finset.Ico 0 N, f i • g i‖ =
        ‖f (N - 1) • (∑ i ∈ Finset.range N, g i) -
          f 0 • (∑ i ∈ Finset.range 0, g i) -
          ∑ i ∈ Finset.Ico 0 (N - 1),
            (f (i + 1) - f i) •
              (∑ j ∈ Finset.range (i + 1), g j)‖ :=
      congrArg norm hparts
    _ = ‖(f (N - 1) : ℂ) * (∑ i ∈ Finset.range N, g i) -
        ∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (i + 1), g j)‖ := by
      simp only [Finset.sum_range_zero, Complex.real_smul, mul_zero, sub_zero]
    _ ≤ ‖(f (N - 1) : ℂ) * (∑ i ∈ Finset.range N, g i)‖ +
        ‖∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sub_le _ _
    _ ≤ f (N - 1) * B +
        ∑ i ∈ Finset.Ico 0 (N - 1), (f (i + 1) - f i) * B := by
      apply add_le_add
      · rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hf (N - 1) (by omega))]
        exact mul_le_mul_of_nonneg_left (hpartial N le_rfl)
          (hf (N - 1) (by omega))
      · calc
          ‖∑ i ∈ Finset.Ico 0 (N - 1),
              ((f (i + 1) - f i : ℝ) : ℂ) *
                (∑ j ∈ Finset.range (i + 1), g j)‖ ≤
              ∑ i ∈ Finset.Ico 0 (N - 1),
                ‖((f (i + 1) - f i : ℝ) : ℂ) *
                  (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.Ico 0 (N - 1),
              (f (i + 1) - f i) * B := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' := Finset.mem_Ico.mp hi
            rw [norm_mul, norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr (hmono i (by omega)))]
            exact mul_le_mul_of_nonneg_left (hpartial (i + 1) (by omega))
              (sub_nonneg.mpr (hmono i (by omega)))
    _ = (2 * f (N - 1) - f 0) * B := by
      have htel : ∑ i ∈ Finset.Ico 0 (N - 1),
          (f (i + 1) - f i) = f (N - 1) - f 0 := by
        rw [Nat.Ico_zero_eq_range, Finset.sum_range_sub]
      rw [← Finset.sum_mul, htel]
      ring
    _ ≤ 2 * f (N - 1) * B := by
      have hf0 : 0 ≤ f 0 := hf 0 hN
      nlinarith

/-- Exact range form of one dyadic block of the normalized reflected
polynomial.  The `min` records the literal truncation at the natural dual
cutoff `M`; no coefficient beyond that cutoff is retained. -/
theorem dirichletPoly_normalizedTypeIReflectedCoeff_eq_range
    (sigma t : ℝ) (P M : ℕ) (hP : 0 < P) (hPM : P < M) :
    dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t =
      ∑ i ∈ Finset.range (min P (M - P)),
        (((P + 1 + i : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) •
          unitaryPhase (logarithmicPhase t (P + 1 + i)) := by
  have hInterval : Finset.Ioc P (2 * P) =
      Finset.Ico (P + 1) (2 * P + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  unfold dirichletPoly dyadicInterval
  rw [hInterval, Finset.sum_Ico_eq_sum_range]
  have hLength : 2 * P + 1 - (P + 1) = P := by omega
  rw [hLength]
  push_cast
  symm
  calc
    ∑ i ∈ Finset.range (min P (M - P)),
        (((P : ℝ) + 1 + (i : ℝ)) ^ sigma / (M : ℝ) ^ sigma) •
          unitaryPhase (logarithmicPhase t (P + 1 + i)) =
      ∑ i ∈ Finset.range (min P (M - P)),
        normalizedTypeIReflectedCoeff sigma M (P + 1 + i) *
          ((P : ℂ) + 1 + (i : ℂ)) ^ (-t * I) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiL : i < min P (M - P) := Finset.mem_range.mp hi
      have hiDiff : i < M - P := lt_of_lt_of_le hiL (min_le_right _ _)
      have hnPos : 0 < P + 1 + i := by omega
      have hnM : P + 1 + i ≤ M := by omega
      rw [normalizedTypeIReflectedCoeff, ite_eq_left ⟨by omega, hnM⟩,
        Complex.real_smul]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hPhase :=
        unitaryPhase_logarithmicPhase_eq_cpow t (P + 1 + i) hnPos
      norm_num only [Nat.cast_add, Nat.cast_one] at hPhase
      rw [hPhase]
    _ = ∑ i ∈ Finset.range P,
        normalizedTypeIReflectedCoeff sigma M (P + 1 + i) *
          ((P : ℂ) + 1 + (i : ℂ)) ^ (-t * I) := by
      apply Finset.sum_subset
      · intro i hi
        exact Finset.mem_range.mpr
          ((Finset.mem_range.mp hi).trans_le (min_le_left _ _))
      · intro i hiP hiL
        have hiP' : i < P := Finset.mem_range.mp hiP
        have hiLower : min P (M - P) ≤ i := by
          exact le_of_not_gt (fun h => hiL (Finset.mem_range.mpr h))
        have hMin : min P (M - P) = M - P := by
          apply min_eq_right
          omega
        have hnM : M < P + 1 + i := by
          rw [hMin] at hiLower
          omega
        rw [normalizedTypeIReflectedCoeff,
          ite_eq_right (fun h => (Nat.not_le_of_lt hnM) h.2), zero_mul]

/-- Weyl bound for the actual increasing normalized coefficient on a retained
reflected dyadic interval.  Abel summation is applied in the increasing form,
so the normalization by `M^sigma` is used rather than discarded. -/
theorem norm_dirichletPoly_normalizedTypeIReflectedCoeff_le_weyl
    (sigma t : ℝ) (P M : ℕ)
    (hsigma : 0 ≤ sigma) (hP : 0 < P) (hPM : P < M)
    (htOne : 1 ≤ t)
    (hPt : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ t)
    (htP : t ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ ≤
      60 * Real.sqrt (((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
  let Y : ℝ := t ^ (1 / 3 : ℝ)
  let L : ℕ := min P (M - P)
  let f : ℕ → ℝ := fun i =>
    ((P + 1 + i : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma
  let g : ℕ → ℂ := fun i =>
    unitaryPhase (logarithmicPhase t (P + 1 + i))
  have htPos : 0 < t := zero_lt_one.trans_le htOne
  have hYOne : 1 ≤ Y := Real.one_le_rpow htOne (by norm_num)
  have hYcube : Y ^ (3 : ℕ) = t := by
    dsimp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htPos.le]
    norm_num
  have hYUpper : Y ≤ ((P + 1 : ℕ) : ℝ) := by
    have hRoot := Real.rpow_le_rpow htPos.le htP
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hBasePos : (0 : ℝ) < (P + 1 : ℕ) := by positivity
    have hRight :
        ((((P + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) =
          ((P + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBasePos.le]
      norm_num
    simpa only [Y, hRight] using hRoot
  have hLPos : 0 < L := by
    dsimp only [L]
    exact lt_min hP (Nat.sub_pos_of_lt hPM)
  have hLUpper : L ≤ P + 1 := by
    dsimp only [L]
    exact (min_le_left _ _).trans (Nat.le_succ _)
  have hPartial : ∀ j, j ≤ L →
      ‖∑ i ∈ Finset.range j, g i‖ ≤
        30 * Real.sqrt (((P + 1 : ℕ) : ℝ) * Y) := by
    intro j hj
    dsimp only [g]
    have hWeyl := logarithmic_weyl_exponent_pair_prefix Y (P + 1) j
      hYOne (by omega) hYUpper (by simpa only [hYcube] using hPt)
      (hj.trans hLUpper)
    rw [logarithmicSum_eq_sum_range] at hWeyl
    norm_num only [Nat.cast_add, Nat.cast_one] at hWeyl
    rw [hYcube] at hWeyl
    simpa only [Nat.cast_add, Nat.cast_one] using hWeyl
  have hFNonneg : ∀ i, i < L → 0 ≤ f i := by
    intro i _hi
    dsimp only [f]
    positivity
  have hFMono : ∀ i, i + 1 < L → f i ≤ f (i + 1) := by
    intro i _hi
    dsimp only [f]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast (show P + 1 + i ≤ P + 1 + (i + 1) by omega)
    · exact hsigma
  have hAbel := norm_weighted_sum_le_of_monotone f g L
    (30 * Real.sqrt (((P + 1 : ℕ) : ℝ) * Y))
    hLPos hFNonneg hFMono hPartial
  have hLastIndex : P + 1 + (L - 1) ≤ M := by
    have hLToDiff : L ≤ M - P := min_le_right _ _
    omega
  have hFLast : f (L - 1) ≤ 1 := by
    dsimp only [f]
    have hMPos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    rw [div_le_one (Real.rpow_pos_of_pos hMPos _)]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hLastIndex) hsigma
  rw [dirichletPoly_normalizedTypeIReflectedCoeff_eq_range
    sigma t P M hP hPM]
  change ‖∑ i ∈ Finset.range L, f i • g i‖ ≤ _
  calc
    ‖∑ i ∈ Finset.range L, f i • g i‖ ≤
        2 * f (L - 1) *
          (30 * Real.sqrt (((P + 1 : ℕ) : ℝ) * Y)) := hAbel
    _ ≤ 2 * 1 * (30 * Real.sqrt (((P + 1 : ℕ) : ℝ) * Y)) := by
      gcongr
    _ = 60 * Real.sqrt (((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
      dsimp only [Y]
      ring

/-- Boundary-slack version of the weighted reflected Weyl estimate.  The
factor `X` is retained explicitly through the A--B process, so the natural
dual cutoff may differ from its ideal real scale by a proved power loss. -/
theorem norm_dirichletPoly_normalizedTypeIReflectedCoeff_le_weyl_with_slack
    (sigma t X : ℝ) (P M : ℕ)
    (hsigma : 0 ≤ sigma) (hP : 0 < P) (hPM : P < M)
    (htOne : 1 ≤ t) (hX : 1 ≤ X)
    (hPt : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ X * t)
    (htP : t ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ ≤
      60 * (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) *
        Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
  let Y : ℝ := t ^ (1 / 3 : ℝ)
  let L : ℕ := min P (M - P)
  let f : ℕ → ℝ := fun i =>
    ((P + 1 + i : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma
  let g : ℕ → ℂ := fun i =>
    unitaryPhase (logarithmicPhase t (P + 1 + i))
  have htPos : 0 < t := zero_lt_one.trans_le htOne
  have hYOne : 1 ≤ Y := Real.one_le_rpow htOne (by norm_num)
  have hYcube : Y ^ (3 : ℕ) = t := by
    dsimp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htPos.le]
    norm_num
  have hYUpper : Y ≤ ((P + 1 : ℕ) : ℝ) := by
    have hRoot := Real.rpow_le_rpow htPos.le htP
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hBasePos : (0 : ℝ) < (P + 1 : ℕ) := by positivity
    have hRight :
        ((((P + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) =
          ((P + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBasePos.le]
      norm_num
    simpa only [Y, hRight] using hRoot
  have hLPos : 0 < L := by
    dsimp only [L]
    exact lt_min hP (Nat.sub_pos_of_lt hPM)
  have hLUpper : L ≤ P + 1 := by
    dsimp only [L]
    exact (min_le_left _ _).trans (Nat.le_succ _)
  have hPartial : ∀ j, j ≤ L →
      ‖∑ i ∈ Finset.range j, g i‖ ≤
        30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y) := by
    intro j hj
    dsimp only [g]
    have hWeyl := logarithmic_weyl_exponent_pair_prefix_with_slack
      Y X (P + 1) j hYOne hX (by omega) hYUpper
      (by simpa only [hYcube] using hPt) (hj.trans hLUpper)
    rw [logarithmicSum_eq_sum_range] at hWeyl
    norm_num only [Nat.cast_add, Nat.cast_one] at hWeyl
    rw [hYcube] at hWeyl
    simpa only [Nat.cast_add, Nat.cast_one] using hWeyl
  have hFNonneg : ∀ i, i < L → 0 ≤ f i := by
    intro i _hi
    dsimp only [f]
    positivity
  have hFMono : ∀ i, i + 1 < L → f i ≤ f (i + 1) := by
    intro i _hi
    dsimp only [f]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast (show P + 1 + i ≤ P + 1 + (i + 1) by omega)
    · exact hsigma
  have hAbel := norm_weighted_sum_le_of_monotone f g L
    (30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y))
    hLPos hFNonneg hFMono hPartial
  have hLastTwo : P + 1 + (L - 1) ≤ 2 * (P + 1) := by
    have hLP : L ≤ P := min_le_left _ _
    omega
  have hFLast : f (L - 1) ≤
      (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) := by
    dsimp only [f]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hLastTwo) hsigma
  rw [dirichletPoly_normalizedTypeIReflectedCoeff_eq_range
    sigma t P M hP hPM]
  change ‖∑ i ∈ Finset.range L, f i • g i‖ ≤ _
  calc
    ‖∑ i ∈ Finset.range L, f i • g i‖ ≤
        2 * f (L - 1) *
          (30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y)) := hAbel
    _ ≤ 2 * ((((2 * (P + 1) : ℕ) : ℝ) ^ sigma /
          (M : ℝ) ^ sigma)) *
          (30 * Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * Y)) := by
      gcongr
    _ = 60 * (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) *
        Real.sqrt (X * ((P + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) := by
      dsimp only [Y]
      ring

/-- Physical-scale form of the reflected Weyl estimate.  The exact scale
identity eliminates the dyadic length, while the harmless factor `4^sigma`
accounts for the sharp endpoint and normalization. -/
theorem norm_normalizedTypeIReflectedCoeff_le_physical_weyl
    {sigma d T theta w : ℝ} {P M : ℕ}
    (hsigma : 0 ≤ sigma) (hd : 0 ≤ d) (hT : 1 ≤ T)
    (hP : 1 < P) (hPM : P < M)
    (htheta : 0 < theta) (hScale : (P : ℝ) ^ theta = T)
    (hwOne : 1 ≤ w) (hwUpper : w ≤ 3 * T)
    (hPt : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
      (2 * T ^ (4 * d)) * w)
    (htP : w ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) w‖ ≤
      (60 * 4 ^ sigma * Real.sqrt 12) *
        T ^ (2 * d + 1 / (2 * theta) + 1 / 6) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hPReal : (1 : ℝ) < P := by exact_mod_cast hP
  have hMPos : (0 : ℝ) < M := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (lt_trans hP hPM))
  have hXOne : (1 : ℝ) ≤ 2 * T ^ (4 * d) := by
    have hPow : 1 ≤ T ^ (4 * d) := Real.one_le_rpow hT (by positivity)
    nlinarith
  have hRaw := norm_dirichletPoly_normalizedTypeIReflectedCoeff_le_weyl_with_slack
    sigma w (2 * T ^ (4 * d)) P M hsigma (by omega) hPM hwOne hXOne hPt htP
  have hRatio :
      (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) ≤
        4 ^ sigma := by
    have hPMCast : (((2 * (P + 1) : ℕ) : ℝ)) ≤ 4 * (M : ℝ) := by
      exact_mod_cast (show 2 * (P + 1) ≤ 4 * M by omega)
    have hPow := Real.rpow_le_rpow (by positivity) hPMCast hsigma
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hMPos.le] at hPow
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hMPos sigma)).2 (by
      simpa only [mul_assoc] using hPow)
  have hPEq : (P : ℝ) = T ^ (1 / theta) :=
    calc
      (P : ℝ) = ((P : ℝ) ^ theta) ^ (1 / theta) := by
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ P)]
        field_simp [htheta.ne']
        exact (Real.rpow_one _).symm
      _ = T ^ (1 / theta) := by rw [hScale]
  have hPSucc : ((P + 1 : ℕ) : ℝ) ≤ 2 * T ^ (1 / theta) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [← hPEq]
    nlinarith [hPReal.le]
  have hwThird : w ^ (1 / 3 : ℝ) ≤ 3 * T ^ (1 / 3 : ℝ) := by
    have hRpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ w) hwUpper
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    calc
      w ^ (1 / 3 : ℝ) ≤ (3 * T) ^ (1 / 3 : ℝ) := hRpow
      _ = 3 ^ (1 / 3 : ℝ) * T ^ (1 / 3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTPos.le]
      _ ≤ 3 * T ^ (1 / 3 : ℝ) := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
            (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hInside :
      (2 * T ^ (4 * d)) * ((P + 1 : ℕ) : ℝ) * w ^ (1 / 3 : ℝ) ≤
        12 * T ^ (4 * d + 1 / theta + 1 / 3) := by
    calc
      (2 * T ^ (4 * d)) * ((P + 1 : ℕ) : ℝ) * w ^ (1 / 3 : ℝ) ≤
          (2 * T ^ (4 * d)) * (2 * T ^ (1 / theta)) *
            (3 * T ^ (1 / 3 : ℝ)) := by gcongr
      _ = 12 * T ^ (4 * d + 1 / theta + 1 / 3) := by
        rw [Real.rpow_add hTPos, Real.rpow_add hTPos]
        ring
  have hSqrt := Real.sqrt_le_sqrt hInside
  have hSqrtRewrite :
      Real.sqrt (12 * T ^ (4 * d + 1 / theta + 1 / 3)) =
        Real.sqrt 12 * T ^ (2 * d + 1 / (2 * theta) + 1 / 6) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTPos.le]
    congr 1
    field_simp [htheta.ne']
    ring
  calc
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) w‖ ≤
        60 * (((2 * (P + 1) : ℕ) : ℝ) ^ sigma / (M : ℝ) ^ sigma) *
          Real.sqrt ((2 * T ^ (4 * d)) * ((P + 1 : ℕ) : ℝ) *
            w ^ (1 / 3 : ℝ)) := hRaw
    _ ≤ 60 * 4 ^ sigma *
          Real.sqrt (12 * T ^ (4 * d + 1 / theta + 1 / 3)) := by gcongr
    _ = (60 * 4 ^ sigma * Real.sqrt 12) *
          T ^ (2 * d + 1 / (2 * theta) + 1 / 6) := by
      rw [hSqrtRewrite]
      ring

/-- The normalized reflected coefficients are real, hence fixed by the
coefficientwise conjugation used to reverse the sign of an ordinate. -/
theorem conjugateCoeffs_normalizedTypeIReflectedCoeff
    (sigma : ℝ) (M : ℕ) :
    conjugateCoeffs (normalizedTypeIReflectedCoeff sigma M) =
      normalizedTypeIReflectedCoeff sigma M := by
  funext n
  unfold conjugateCoeffs normalizedTypeIReflectedCoeff
  split_ifs <;> simp

/-- Reversing the ordinate preserves the norm of a normalized reflected
block.  This is the exact bridge for the negative Poisson half. -/
theorem norm_dirichletPoly_normalizedTypeIReflectedCoeff_neg
    (sigma t : ℝ) (P M : ℕ) :
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (-t)‖ =
      ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ := by
  have hSource :
      sourceDirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t =
        dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (-t) := by
    unfold sourceDirichletPoly dirichletPoly
    apply Finset.sum_congr rfl
    intro n _hn
    congr 2
    push_cast
    ring
  calc
    ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (-t)‖ =
        ‖sourceDirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ :=
      congrArg norm hSource.symm
    _ = ‖sourceDirichletPoly P
          (conjugateCoeffs (normalizedTypeIReflectedCoeff sigma M)) t‖ := by
      rw [conjugateCoeffs_normalizedTypeIReflectedCoeff]
    _ = ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t‖ :=
      norm_sourceDirichletPoly_conjugateCoeffs _ _ _

/-- The translated negative Poisson block has the norm of the same real
coefficient block at the positive reflected ordinate `3T-v`. -/
theorem norm_phaseShifted_normalized_reflected_eq
    (sigma T v : ℝ) (P M : ℕ) :
    ‖dirichletPoly P
        (phaseShiftCoeffs (-3 * T)
          (normalizedTypeIReflectedCoeff sigma M)) v‖ =
      ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) (3 * T - v)‖ := by
  rw [← dirichletPoly_translate]
  convert norm_dirichletPoly_normalizedTypeIReflectedCoeff_neg
    sigma (3 * T - v) P M using 2
  all_goals ring_nf

/-- One cancellation-safe interface for the two retained Poisson signs.
The coefficient sequence is existential because the negative sign carries
the fixed translation by `-3T`, whereas the positive sign does not.  The
last field identifies its norm with the same normalized reflected block at
an actual positive ordinate in `[T/2,5T/2]`; this is the bridge needed by
the Weyl alternative after the finite sign and displacement selections. -/
theorem extract_common_signed_reflected_block
    {M : ℕ} {sigma T D H S : ℝ} (W : Finset ℝ)
    (hM : 1 < M) (hsigma : 0 ≤ sigma) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hDH : D + H ≤ T / 2)
    (hSeparated : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, T - D ≤ t ∧ t ≤ 2 * T + D)
    (hEach : ∀ t ∈ W,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
      ∃ a : ℕ → ℂ,
        IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
        (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
        W.card ≤ 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
          (Nat.clog 2 M) * U.card ∧
        (∀ n ∈ dyadicInterval (2 ^ j), ‖a n‖ ≤ 1) ∧
        (∀ v ∈ U, S / Nat.clog 2 M ≤ ‖dirichletPoly (2 ^ j) a v‖) ∧
        (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
          ‖dirichletPoly (2 ^ j) a v‖ =
            ‖dirichletPoly (2 ^ j)
              (normalizedTypeIReflectedCoeff sigma M) w‖) := by
  rcases select_common_signed_reflected_family W hEach with
    ⟨Wsign, hWsign, hSignCard, hNegative⟩ |
      ⟨Wsign, hWsign, hSignCard, hPositive⟩
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hNegative
    let a : ℕ → ℂ := phaseShiftCoeffs (-3 * T)
      (normalizedTypeIReflectedCoeff sigma M)
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      rw [norm_phaseShiftCoeffs]
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨3 * T - v, ?_, ?_⟩
      · rw [Set.mem_Icc]
        have hvRange := hURange v hv
        constructor <;> linarith
      · dsimp only [a]
        exact norm_phaseShifted_normalized_reflected_eq sigma T v (2 ^ j) M
  · have hSepSign : IsSeparated 1 Wsign := by
      intro x hx y hy hxy
      exact hSeparated x (hWsign hx) y (hWsign hy) hxy
    have hRangeSign : ∀ t ∈ Wsign,
        T - D ≤ t ∧ t ≤ 2 * T + D := by
      intro t ht
      exact hRange t (hWsign ht)
    obtain ⟨j, hj, U, hSepU, hBaseU, hURange, hCardU, hLargeU⟩ :=
      extract_common_positive_reflected_mhh_block Wsign hM hH hT hDH
        hSepSign hRangeSign hPositive
    let a : ℕ → ℂ := normalizedTypeIReflectedCoeff sigma M
    refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, ?_, ?_, ?_, ?_⟩
    · calc
        W.card ≤ 2 * Wsign.card := hSignCard
        _ ≤ 2 * ((2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card) := by gcongr
        _ = 2 * (2 * (2 * ⌈H⌉₊ + 1)) *
            (Nat.clog 2 M) * U.card := by ring
    · intro n hn
      dsimp only [a]
      exact norm_normalizedTypeIReflectedCoeff_le_one hsigma
        (lt_trans Nat.zero_lt_one hM)
    · exact hLargeU
    · intro v hv
      refine ⟨v, hURange v hv, ?_⟩
      rfl

/-- Abel summation on a literal natural interval.  This is the interval
counterpart of `norm_weighted_sum_le_of_antitone`; keeping the endpoints in
the statement avoids replacing a terminal source block by a prefix beginning
at one. -/
theorem norm_weighted_Ioc_le_of_antitone
    (f : ℕ → ℝ) (g : ℕ → ℂ) (L U : ℕ) (B : ℝ)
    (hLU : L < U)
    (hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n)
    (hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n)
    (hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ ≤ f (L + 1) * B := by
  have hLen : 0 < U - L := Nat.sub_pos_of_lt hLU
  let F : ℕ → ℝ := fun i => f (L + 1 + i)
  let G : ℕ → ℂ := fun i => g (L + 1 + i)
  have hF : ∀ i, i < U - L → 0 ≤ F i := by
    intro i hi
    exact hf _ (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
  have hAntiF : ∀ i, i + 1 < U - L → F (i + 1) ≤ F i := by
    intro i hi
    simpa only [F, Nat.add_assoc] using
      hanti (L + 1 + i) (by omega) (by omega)
  have hBound := norm_weighted_sum_le_of_antitone F G (U - L) B
    hLen hF hAntiF (by
      intro j hj
      simpa only [G] using hpartial j hj)
  have hIoc : Finset.Ioc L U = Finset.Ico (L + 1) (U + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : U + 1 - (L + 1) = U - L := by omega
  rw [hLength]
  simpa only [F, G, Nat.cast_add, Nat.cast_one] using hBound

/-- The fixed smooth step used by the Type-I partition is decreasing. -/
theorem antitone_typeISmoothStep : Antitone typeISmoothStep := by
  intro x y hxy
  unfold typeISmoothStep
  exact Real.smoothTransition.monotone (by linarith)

theorem typeISmoothStep_nonneg (x : ℝ) : 0 ≤ typeISmoothStep x := by
  unfold typeISmoothStep
  exact Real.smoothTransition.nonneg _

theorem typeISmoothStep_le_one (x : ℝ) : typeISmoothStep x ≤ 1 := by
  unfold typeISmoothStep
  exact Real.smoothTransition.le_one _

theorem typeIDyadicCutoff_eq_one_sub_step_of_le
    {x : ℝ} (hx : x ≤ 1) :
    typeIDyadicCutoff x = 1 - typeISmoothStep (2 * x) := by
  rw [typeIDyadicCutoff, typeISmoothStep_eq_one hx]

theorem typeIDyadicCutoff_eq_step_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    typeIDyadicCutoff x = typeISmoothStep x := by
  have hzero : typeISmoothStep (2 * x) = 0 :=
    typeISmoothStep_eq_zero (by linarith)
  rw [typeIDyadicCutoff, hzero]
  ring

/-- Real-power deweighting of one source term into the unitary logarithmic
phase used by all finite Abel estimates. -/
theorem source_weighted_cpow_eq_smul_phase
    (w σ t : ℝ) {n : ℕ} (hn : 0 < n) :
    (w : ℂ) * (n : ℂ) ^ (-(σ : ℂ)) *
        (n : ℂ) ^ (-(t : ℂ) * I) =
      (w * (n : ℝ) ^ (-σ)) •
        unitaryPhase (logarithmicPhase t n) := by
  rw [Complex.real_smul,
    unitaryPhase_logarithmicPhase_eq_cpow t n hn]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp only [Complex.ofReal_natCast]
  push_cast
  ring

/-- A decreasing smooth cutoff can be inserted into the Abel-summed
second-derivative estimate without changing its square-root majorant. -/
theorem norm_smoothStep_weighted_Ioc_le_sqrt
    (c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLU : L < U) (hLength : U - L ≤ L)
    (hLt : (L : ℝ) ≤ t) (htL : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
  let f : ℕ → ℝ := fun n =>
    typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    dsimp only [f]
    exact mul_nonneg (typeISmoothStep_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    have hnPos : 0 < n := lt_trans hL hnL
    have harg : c * (n : ℝ) / Q ≤ c * ((n + 1 : ℕ) : ℝ) / Q := by
      apply div_le_div_of_nonneg_right _ hQReal.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hc
    have hstep := antitone_typeISmoothStep harg
    have hpow : ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast Nat.le_succ n
      · linarith
    dsimp only [f]
    exact mul_le_mul hstep hpow (Real.rpow_nonneg (by positivity) _)
      (typeISmoothStep_nonneg _)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤ 100 * Real.sqrt t := by
    intro j hj
    dsimp only [g]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using
      norm_logarithmicPhase_prefix_le_sqrt L j t hL
        (hj.trans hLength) hLt htL
  have hBound := norm_weighted_Ioc_le_of_antitone f g L U
    (100 * Real.sqrt t) hLU hf hanti hpartial
  have hStepOne : typeISmoothStep
      (c * (((L + 1 : ℕ) : ℝ)) / Q) ≤ 1 := typeISmoothStep_le_one _
  have hPowNonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ =
        ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ := by rfl
    _ ≤ f (L + 1) * (100 * Real.sqrt t) := hBound
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
      dsimp only [f]
      gcongr
      exact mul_le_of_le_one_left hPowNonneg hStepOne
    _ = (L + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by norm_num

/-- Weyl A--B-process companion to the preceding smooth-weight Abel bound.
It applies to the exact monotone cutoff occurring in a classified source
block and retains the physical ordinate `t`. -/
theorem norm_smoothStep_weighted_Ioc_le_weyl
    (X c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLU : L < U) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (hX : 1 ≤ X)
    (hSquare : (((L + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ X * t)
    (hCube : t ≤ (((L + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
  let f : ℕ → ℝ := fun n =>
    typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  let Y : ℝ := t ^ (1 / 3 : ℝ)
  have htPos : 0 < t := zero_lt_one.trans_le htOne
  have hYOne : 1 ≤ Y := Real.one_le_rpow htOne (by norm_num)
  have hYcube : Y ^ (3 : ℕ) = t := by
    dsimp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htPos.le]
    norm_num
  have hYUpper : Y ≤ ((L + 1 : ℕ) : ℝ) := by
    have hRoot := Real.rpow_le_rpow htPos.le hCube
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hBasePos : (0 : ℝ) < (L + 1 : ℕ) := by positivity
    have hRight :
        ((((L + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) =
          ((L + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBasePos.le]
      norm_num
    simpa only [Y, hRight] using hRoot
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    dsimp only [f]
    exact mul_nonneg (typeISmoothStep_nonneg _)
      (Real.rpow_nonneg (by positivity) _)
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    have hnPos : 0 < n := lt_trans hL hnL
    have harg : c * (n : ℝ) / Q ≤ c * ((n + 1 : ℕ) : ℝ) / Q := by
      apply div_le_div_of_nonneg_right _ hQReal.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hc
    have hstep := antitone_typeISmoothStep harg
    have hpow : ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast Nat.le_succ n
      · linarith
    dsimp only [f]
    exact mul_le_mul hstep hpow (Real.rpow_nonneg (by positivity) _)
      (typeISmoothStep_nonneg _)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤
        30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y) := by
    intro j hj
    dsimp only [g]
    have hWeyl := logarithmic_weyl_exponent_pair_prefix_with_slack
      Y X (L + 1) j hYOne hX (by omega) hYUpper
      (by simpa only [hYcube] using hSquare)
      (hj.trans hLength |>.trans (Nat.le_succ L))
    rw [logarithmicSum_eq_sum_range] at hWeyl
    rw [hYcube] at hWeyl
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using hWeyl
  have hBound := norm_weighted_Ioc_le_of_antitone f g L U
    (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y)) hLU hf hanti hpartial
  have hStepOne : typeISmoothStep
      (c * (((L + 1 : ℕ) : ℝ)) / Q) ≤ 1 := typeISmoothStep_le_one _
  have hPowNonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ =
        ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ := by rfl
    _ ≤ f (L + 1) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y)) := hBound
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * Y)) := by
      dsimp only [f]
      gcongr
      exact mul_le_of_le_one_left hPowNonneg hStepOne
    _ = ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
      rfl

/-- Uncut specialization of the smooth Weyl estimate, used for the middle
term in the exact three-sum source expansion. -/
theorem norm_plain_weighted_Ioc_le_weyl
    (X σ t : ℝ) (L U : ℕ)
    (hσ : 0 ≤ σ) (hL : 0 < L) (hLU : L < U)
    (hLength : U - L ≤ L) (htOne : 1 ≤ t) (hX : 1 ≤ X)
    (hSquare : (((L + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ X * t)
    (hCube : t ≤ (((L + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (X * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
  have h := norm_smoothStep_weighted_Ioc_le_weyl
    X 0 σ t 1 L U (by norm_num) hσ (by omega) hL hLU hLength
      htOne hX hSquare hCube
  have hEq :
      (∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (0 * (n : ℝ) / 1) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (0 : ℝ) * (n : ℝ) / 1 = 0 by ring,
      typeISmoothStep_eq_one (by norm_num : (0 : ℝ) ≤ 1), one_mul]
  rw [hEq]
  simpa only [Nat.cast_one] using h

/-- Exact three-sum form of a source block whose upper tail boundary meets
the sharp cutoff.  The rising half of the annular cutoff is written as the
difference of two decreasing weights, and the falling half is already a
decreasing smooth step. -/
theorem typeISourceSmoothBlock_eq_terminal_three_sums
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y)
    (hLower : 2 * (Y + 1) ≤ 2 ^ r * Y) :
    let Q := 2 ^ r * Y
    typeISourceSmoothBlock Y A r σ t =
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) +
      (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) := by
  dsimp only
  let Q : ℕ := 2 ^ r * Y
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hYHalf : Y ≤ Q / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
    omega
  have hYQ : Y ≤ Q := hYHalf.trans (Nat.div_le_self Q 2)
  have hLowerSubset : Finset.Ioc (Q / 2) (min Q A) ⊆
      Finset.Ioc Y (min Q A) := by
    intro n hn
    have hndata := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hYHalf.trans_lt hndata.1, hndata.2⟩
  have hRestricted :
      (∑ n ∈ Finset.Ioc Y (min Q A),
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    rw [← Finset.sum_subset hLowerSubset]
    intro n hn hnSmall
    have hnData := Finset.mem_Ioc.mp hn
    have hnHalf : n ≤ Q / 2 := by
      by_contra hnot
      exact hnSmall (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnot, hnData.2⟩)
    have hRatio : (n : ℝ) / Q ≤ 1 / 2 := by
      rw [div_le_iff₀ (by exact_mod_cast hQ)]
      have hnTwice : 2 * n ≤ Q :=
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hnHalf
      have hnTwiceReal : (2 : ℝ) * n ≤ Q := by exact_mod_cast hnTwice
      nlinarith
    rw [typeIDyadicCutoff_eq_zero_of_le_half hRatio, zero_mul, zero_smul]
  have hLowerExpand :
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc (Q / 2) (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnQ : n ≤ Q :=
      (Finset.mem_Ioc.mp hn).2.trans (min_le_left Q A)
    have hRatio : (n : ℝ) / Q ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hQ)]
      exact_mod_cast hnQ
    rw [typeIDyadicCutoff_eq_one_sub_step_of_le hRatio]
    rw [sub_mul, one_mul, sub_smul]
    simp only [mul_div_assoc]
  have hUpperExpand :
      (∑ n ∈ Finset.Ioc Q A,
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnQ : Q < n := (Finset.mem_Ioc.mp hn).1
    have hRatio : 1 ≤ (n : ℝ) / Q := by
      rw [le_div_iff₀ (by exact_mod_cast hQ)]
      norm_num
      exact_mod_cast hnQ.le
    rw [typeIDyadicCutoff_eq_step_of_one_le hRatio]
  rw [typeISourceSmoothBlock_eq_restricted]
  have hCpow :
      (∑ n ∈ Finset.Ioc Y A,
        (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
          (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc Y A,
        (typeIDyadicCutoff ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact source_weighted_cpow_eq_smul_phase _ σ t
      (lt_trans hY (Finset.mem_Ioc.mp hn).1)
  change (∑ n ∈ Finset.Ioc Y A,
      (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)) = _
  rw [hCpow]
  by_cases hQA : Q ≤ A
  · have hUnion : Finset.Ioc Y Q ∪ Finset.Ioc Q A = Finset.Ioc Y A :=
      Finset.Ioc_union_Ioc_eq_Ioc hYQ hQA
    have hDisjoint : Disjoint (Finset.Ioc Y Q) (Finset.Ioc Q A) :=
      Finset.Ioc_disjoint_Ioc_of_le le_rfl
    rw [← hUnion, Finset.sum_union hDisjoint]
    have hMin : min Q A = Q := min_eq_left hQA
    rw [hMin] at hRestricted hLowerExpand
    rw [hRestricted, hLowerExpand, hUpperExpand]
    rw [min_eq_left hQA]
  · have hAQ : A < Q := lt_of_not_ge hQA
    have hMin : min Q A = A := min_eq_right hAQ.le
    have hUpperEmpty : Finset.Ioc Q A = ∅ := by
      ext n
      simp
      omega
    rw [hMin] at hRestricted hLowerExpand
    rw [hRestricted, hLowerExpand]
    rw [hMin]
    rw [hUpperEmpty, Finset.sum_empty, add_zero]

/-- The coefficient-one member of the three-sum terminal decomposition obeys
the same interval Abel bound as its smooth companions. -/
theorem norm_plain_weighted_Ioc_le_sqrt
    {L U : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (hLU : L < U) (hL : 0 < L)
    (hLength : U - L ≤ L) (hLt : (L : ℝ) ≤ t)
    (htL : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
  let f : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    dsimp only [f]
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (lt_trans hL hnL))
      (by exact_mod_cast Nat.le_succ n) (neg_nonpos.mpr hσ)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤ 100 * Real.sqrt t := by
    intro j hj
    dsimp only [g]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using
      norm_logarithmicPhase_prefix_le_sqrt L j t hL
        (hj.trans hLength) hLt htL
  simpa only [f, g, Nat.cast_add, Nat.cast_one] using
    norm_weighted_Ioc_le_of_antitone f g L U
      (100 * Real.sqrt t) hLU hf hanti hpartial

/-- First-derivative companion to `norm_smoothStep_weighted_Ioc_le_sqrt`.
It covers a terminal interval beginning to the right of the ordinate. -/
theorem norm_smoothStep_weighted_Ioc_le_div
    (c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLU : L < U) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (htL : t ≤ (L : ℝ)) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (L : ℝ) / t) := by
  let f : ℕ → ℝ := fun n =>
    typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    dsimp only [f]
    exact mul_nonneg (typeISmoothStep_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    have hnPos : 0 < n := lt_trans hL hnL
    have harg : c * (n : ℝ) / Q ≤ c * ((n + 1 : ℕ) : ℝ) / Q := by
      apply div_le_div_of_nonneg_right _ hQReal.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hc
    have hstep := antitone_typeISmoothStep harg
    have hpow : ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ) := by
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hnPos)
        (by exact_mod_cast Nat.le_succ n) (neg_nonpos.mpr hσ)
    dsimp only [f]
    exact mul_le_mul hstep hpow (Real.rpow_nonneg (by positivity) _)
      (typeISmoothStep_nonneg _)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤
        6 * Real.pi * (L : ℝ) / t := by
    intro j hj
    dsimp only [g]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using
      norm_logarithmicPhase_prefix_le_div L j t hL
        (hj.trans hLength) htOne htL
  have hBound := norm_weighted_Ioc_le_of_antitone f g L U
    (6 * Real.pi * (L : ℝ) / t) hLU hf hanti hpartial
  have hStepOne : typeISmoothStep
      (c * (((L + 1 : ℕ) : ℝ)) / Q) ≤ 1 := typeISmoothStep_le_one _
  have hPowNonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ =
        ‖∑ n ∈ Finset.Ioc L U, f n • g n‖ := by rfl
    _ ≤ f (L + 1) * (6 * Real.pi * (L : ℝ) / t) := hBound
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) *
        (6 * Real.pi * (L : ℝ) / t) := by
      dsimp only [f]
      gcongr
      exact mul_le_of_le_one_left hPowNonneg hStepOne
    _ = (L + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (L : ℝ) / t) := by norm_num

/-- First-derivative terminal estimate for the coefficient-one member of the
three-sum source decomposition. -/
theorem norm_plain_weighted_Ioc_le_div
    {L U : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (hLU : L < U) (hL : 0 < L)
    (hLength : U - L ≤ L) (htOne : 1 ≤ t)
    (htL : t ≤ (L : ℝ)) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (L : ℝ) / t) := by
  let f : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n => unitaryPhase (logarithmicPhase t n)
  have hf : ∀ n ∈ Finset.Ioc L U, 0 ≤ f n := by
    intro n _hn
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hanti : ∀ n, L < n → n < U → f (n + 1) ≤ f n := by
    intro n hnL _hnU
    dsimp only [f]
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (lt_trans hL hnL))
      (by exact_mod_cast Nat.le_succ n) (neg_nonpos.mpr hσ)
  have hpartial : ∀ j, j ≤ U - L →
      ‖∑ i ∈ Finset.range j, g (L + 1 + i)‖ ≤
        6 * Real.pi * (L : ℝ) / t := by
    intro j hj
    dsimp only [g]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using
      norm_logarithmicPhase_prefix_le_div L j t hL
        (hj.trans hLength) htOne htL
  simpa only [f, g, Nat.cast_add, Nat.cast_one] using
    norm_weighted_Ioc_le_of_antitone f g L U
      (6 * Real.pi * (L : ℝ) / t) hLU hf hanti hpartial

/-- Uniform interval estimate obtained by routing at the physical comparison
`t ≤ L`.  Keeping both nonnegative majorants makes the later terminal source
assembly independent of that case split. -/
theorem norm_plain_weighted_Ioc_le_sqrt_add_div
    {L U : ℕ} {σ t : ℝ}
    (hσ : 0 ≤ σ) (hL : 0 < L) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (htSq : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) *
        (100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t) := by
  by_cases hLU : L < U
  · by_cases htL : t ≤ (L : ℝ)
    · exact (norm_plain_weighted_Ioc_le_div hσ hLU hL hLength htOne htL).trans
        (by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
          nlinarith [Real.sqrt_nonneg t])
    · exact (norm_plain_weighted_Ioc_le_sqrt hσ hLU hL hLength
          (le_of_not_ge htL) htSq).trans (by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
            have hDiv : 0 ≤ 6 * Real.pi * (L : ℝ) / t := by positivity
            linarith)
  · have hEmpty : Finset.Ioc L U = ∅ := by
      ext n
      simp
      omega
    rw [hEmpty, Finset.sum_empty, norm_zero]
    positivity

/-- Smooth-cutoff counterpart of
`norm_plain_weighted_Ioc_le_sqrt_add_div`. -/
theorem norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    (c σ t : ℝ) (Q L U : ℕ)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hQ : 0 < Q)
    (hL : 0 < L) (hLength : U - L ≤ L)
    (htOne : 1 ≤ t) (htSq : t ≤ (L : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.Ioc L U,
        (typeISmoothStep (c * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)‖ ≤
      (L + 1 : ℝ) ^ (-σ) *
        (100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t) := by
  by_cases hLU : L < U
  · by_cases htL : t ≤ (L : ℝ)
    · exact (norm_smoothStep_weighted_Ioc_le_div c σ t Q L U hc hσ hQ
          hL hLU hLength htOne htL).trans (by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
            nlinarith [Real.sqrt_nonneg t])
    · exact (norm_smoothStep_weighted_Ioc_le_sqrt c σ t Q L U hc hσ hQ
          hL hLU hLength (le_of_not_ge htL) htSq).trans
        (by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
          have hDiv : 0 ≤ 6 * Real.pi * (L : ℝ) / t := by positivity
          linarith)
  · have hEmpty : Finset.Ioc L U = ∅ := by
      ext n
      simp
      omega
    rw [hEmpty, Finset.sum_empty, norm_zero]
    positivity

/-- Quantitative elimination bound for a classified upper-edge source block.
The proof uses the exact three-sum identity above and controls all three
pieces without extending the sharp cutoff. -/
theorem norm_typeISourceSmoothBlock_terminal_le
    {Y A r : ℕ} {σ t : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r)
    (hTerminal : A < 2 * (2 ^ r * Y))
    (hσ : 0 ≤ σ) (htOne : 1 ≤ t)
    (htSq : t ≤ (((2 ^ r * Y) / 2 : ℕ) : ℝ) ^ 2) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t +
          6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  have hpowFour : 4 ≤ 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    have hYOne : 1 ≤ Y := hY
    calc
      4 = 4 * 1 := by omega
      _ ≤ 4 * Y := Nat.mul_le_mul_left 4 hYOne
      _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpowFour
  have hQ : 0 < Q := by omega
  have hL : 0 < L := by dsimp only [L]; omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left (by
      exact dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  have hLower : 2 * (Y + 1) ≤ Q := by
    calc
      2 * (Y + 1) ≤ 4 * Y := by omega
      _ ≤ Q := by
        dsimp only [Q]
        exact Nat.mul_le_mul_right Y hpowFour
  have hLowerLength : min Q A - L ≤ L := by omega
  have hUpperLength : A - Q ≤ Q := by omega
  have htSqQ : t ≤ (Q : ℝ) ^ 2 := by
    have hLQ : (L : ℝ) ≤ Q := by exact_mod_cast (Nat.div_le_self Q 2)
    have hSq : (L : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 := by nlinarith
    exact htSq.trans hSq
  let B : ℝ := 100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hPlain := norm_plain_weighted_Ioc_le_sqrt_add_div
    (L := L) (U := min Q A) hσ hL hLowerLength htOne htSq
  have hRise := norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    2 σ t Q L (min Q A) (by norm_num) hσ hQ hL hLowerLength htOne htSq
  have hFall := norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    1 σ t Q Q A (by norm_num) hσ hQ hQ hUpperLength htOne htSqQ
  have hLowerB :
      100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t ≤ B := by
    dsimp only [B]
    have hLQ : (L : ℝ) ≤ Q := by exact_mod_cast (Nat.div_le_self Q 2)
    have htPos : 0 < t := by linarith
    gcongr
  have hWeight : ((Q + 1 : ℕ) : ℝ) ^ (-σ) ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast Nat.add_le_add_right (Nat.div_le_self Q 2) 1
    · linarith
  have hPlain' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hPlain.trans (mul_le_mul_of_nonneg_left hLowerB
          (Real.rpow_nonneg (show 0 ≤ (L : ℝ) + 1 by positivity) (-σ)))
  have hRise' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hRise.trans (mul_le_mul_of_nonneg_left hLowerB
          (Real.rpow_nonneg (show 0 ≤ (L : ℝ) + 1 by positivity) (-σ)))
  have hFall' :
      ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    calc
      _ ≤ ((Q + 1 : ℕ) : ℝ) ^ (-σ) * B := by
        simpa only [B, Nat.cast_add, Nat.cast_one, one_mul] using hFall
      _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
        mul_le_mul_of_nonneg_right hWeight hB
  rw [typeISourceSmoothBlock_eq_terminal_three_sums Y A r σ t hY
    (by simpa only [Q] using hLower)]
  change ‖(∑ n ∈ Finset.Ioc L (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc L (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) +
      (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n))‖ ≤ _
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (((L + 1 : ℕ) : ℝ) ^ (-σ) * B) +
        (((L + 1 : ℕ) : ℝ) ^ (-σ) * B) +
        (((L + 1 : ℕ) : ℝ) ^ (-σ) * B) := by linarith
    _ = 3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t + 6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
      dsimp only [L, Q, B]
      ring

/-- The falling smooth half of a source block stops exactly at `2Q`, even
when the ambient sharp cutoff is larger. -/
theorem source_upper_smooth_sum_eq_min_two_mul
    (Q A : ℕ) (hQ : 0 < Q) (σ t : ℝ) :
    (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) =
      ∑ n ∈ Finset.Ioc Q (min (2 * Q) A),
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n) := by
  have hSub : Finset.Ioc Q (min (2 * Q) A) ⊆ Finset.Ioc Q A := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans (min_le_right _ _)⟩
  rw [← Finset.sum_subset hSub]
  intro n hn hnSmall
  have hnData := Finset.mem_Ioc.mp hn
  have hnTwo : 2 * Q ≤ n := by
    by_contra hnot
    have hnLt : n < 2 * Q := lt_of_not_ge hnot
    exact hnSmall (Finset.mem_Ioc.mpr
      ⟨hnData.1, le_min hnLt.le hnData.2⟩)
  have hRatio : 2 ≤ (n : ℝ) / Q := by
    rw [le_div_iff₀ (by exact_mod_cast hQ)]
    exact_mod_cast hnTwo
  rw [typeISmoothStep_eq_zero hRatio, zero_mul, zero_smul]

/-- Uniform square-root cancellation bound for every classified source
block, with no upper-edge assumption.  The proof uses the exact support at
`2Q`; consequently the ambient sharp cutoff never appears in an interval
length estimate. -/
theorem norm_typeISourceSmoothBlock_le_sqrt
    {Y A r : ℕ} {σ t : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r) (hσ : 0 ≤ σ)
    (htOne : 1 ≤ t)
    (htSq : t ≤ (((2 ^ r * Y) / 2 : ℕ) : ℝ) ^ 2) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t +
          6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  let U : ℕ := min (2 * Q) A
  have hpowFour : 4 ≤ 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    calc
      4 = 4 * 1 := by omega
      _ ≤ 4 * Y := Nat.mul_le_mul_left 4 hY
      _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpowFour
  have hQ : 0 < Q := by omega
  have hL : 0 < L := by dsimp only [L]; omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  have hLower : 2 * (Y + 1) ≤ Q := by
    calc
      2 * (Y + 1) ≤ 4 * Y := by omega
      _ ≤ Q := by
        dsimp only [Q]
        exact Nat.mul_le_mul_right Y hpowFour
  have hLowerLength : min Q A - L ≤ L := by omega
  have hUpperLength : U - Q ≤ Q := by
    dsimp only [U]
    omega
  have htSqQ : t ≤ (Q : ℝ) ^ 2 := by
    have hLQ : (L : ℝ) ≤ Q := by exact_mod_cast (Nat.div_le_self Q 2)
    exact htSq.trans (by nlinarith)
  let B : ℝ := 100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hPlain := norm_plain_weighted_Ioc_le_sqrt_add_div
    (L := L) (U := min Q A) hσ hL hLowerLength htOne htSq
  have hRise := norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    2 σ t Q L (min Q A) (by norm_num) hσ hQ hL hLowerLength htOne htSq
  have hFall := norm_smoothStep_weighted_Ioc_le_sqrt_add_div
    1 σ t Q Q U (by norm_num) hσ hQ hQ hUpperLength htOne htSqQ
  have hLowerB :
      100 * Real.sqrt t + 6 * Real.pi * (L : ℝ) / t ≤ B := by
    dsimp only [B]
    have hLQ : (L : ℝ) ≤ Q := by exact_mod_cast (Nat.div_le_self Q 2)
    have htPos : 0 < t := by linarith
    gcongr
  have hWeight : ((Q + 1 : ℕ) : ℝ) ^ (-σ) ≤
      ((L + 1 : ℕ) : ℝ) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast Nat.add_le_add_right (Nat.div_le_self Q 2) 1
    · linarith
  have hPlain' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hPlain.trans (mul_le_mul_of_nonneg_left hLowerB
        (Real.rpow_nonneg (by positivity) _))
  have hRise' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hRise.trans (mul_le_mul_of_nonneg_left hLowerB
        (Real.rpow_nonneg (by positivity) _))
  have hFall' :
      ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by
    rw [source_upper_smooth_sum_eq_min_two_mul Q A hQ σ t]
    calc
      _ ≤ ((Q + 1 : ℕ) : ℝ) ^ (-σ) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) := by
        simpa only [U, Nat.cast_add, Nat.cast_one, one_mul] using hFall
      _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * B :=
        mul_le_mul_of_nonneg_right hWeight hB
  rw [typeISourceSmoothBlock_eq_terminal_three_sums Y A r σ t hY
    (by simpa only [Q] using hLower)]
  change ‖(∑ n ∈ Finset.Ioc L (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc L (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) +
      (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n))‖ ≤ _
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ (-σ) * B +
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B +
        ((L + 1 : ℕ) : ℝ) ^ (-σ) * B := by linarith
    _ = 3 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t + 6 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ) / t) := by
      dsimp only [L, Q, B]
      ring

/-- Uniform Weyl bound for a complete source-smooth block in the physical
range `Q^2 \lesssim t \lesssim Q^3`.  This theorem consumes the exact
three-sum expansion of the source block, including both smooth boundary
pieces, rather than replacing it by a coefficient-free model. -/
theorem norm_typeISourceSmoothBlock_le_weyl
    {Y A r : ℕ} {σ t : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r)
    (hInterior : 2 * (2 ^ r * Y) ≤ A) (hσ : 0 ≤ σ)
    (htOne : 1 ≤ t)
    (hSquare : ((((2 ^ r * Y) + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t)
    (hCube : t ≤ ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      90 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        Real.sqrt (8 * (((2 ^ r * Y + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ)) := by
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  let U : ℕ := min (2 * Q) A
  let R : ℝ := Real.sqrt (8 * ((Q + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))
  have hpowFour : 4 ≤ 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    calc
      4 = 4 * 1 := by omega
      _ ≤ 4 * Y := Nat.mul_le_mul_left 4 hY
      _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpowFour
  have hQ : 0 < Q := by omega
  have hL : 0 < L := by dsimp only [L]; omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  have hLower : 2 * (Y + 1) ≤ Q := by
    calc
      2 * (Y + 1) ≤ 4 * Y := by omega
      _ ≤ Q := by
        dsimp only [Q]
        exact Nat.mul_le_mul_right Y hpowFour
  have hLowerLength : min Q A - L ≤ L := by omega
  have hUpperLength : U - Q ≤ Q := by
    dsimp only [U]
    omega
  have hLQ : L + 1 ≤ Q + 1 := by omega
  have hLQReal : (((L + 1 : ℕ) : ℝ)) ≤ (((Q + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hLQ
  have hSquareL : (((L + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t := by
    exact (pow_le_pow_left₀ (by positivity) hLQReal 2).trans
      (by simpa only [Q] using hSquare)
  have hSquareQ : (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t := by
    simpa only [Q] using hSquare
  have hCubeQ : t ≤ (((Q + 1 : ℕ) : ℝ) ^ (3 : ℕ)) :=
    hCube.trans (pow_le_pow_left₀ (by positivity) hLQReal 3)
  have hPlain := norm_plain_weighted_Ioc_le_weyl
    8 σ t L (min Q A) hσ hL (by omega) hLowerLength htOne
      (by norm_num) hSquareL
      (by simpa only [L, Q] using hCube)
  have hRise := norm_smoothStep_weighted_Ioc_le_weyl
    8 2 σ t Q L (min Q A) (by norm_num) hσ hQ hL (by omega)
      hLowerLength htOne (by norm_num) hSquareL
      (by simpa only [L, Q] using hCube)
  have hFall := norm_smoothStep_weighted_Ioc_le_weyl
    8 1 σ t Q Q U (by norm_num) hσ hQ hQ (by omega)
      hUpperLength htOne (by norm_num) hSquareQ hCubeQ
  have hRoot :
      Real.sqrt (8 * ((L + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ)) ≤ R := by
    dsimp only [R]
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLQReal (by norm_num))
      (Real.rpow_nonneg (by positivity) _)
  have hWeight : (((Q + 1 : ℕ) : ℝ)) ^ (-σ) ≤
      (((L + 1 : ℕ) : ℝ)) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast hLQ
    · linarith
  have hPlain' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ ≤
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
    exact hPlain.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hRoot (by norm_num))
      (Real.rpow_nonneg (by positivity) _))
  have hRise' :
      ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
    exact hRise.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hRoot (by norm_num))
      (Real.rpow_nonneg (by positivity) _))
  have hFall' :
      ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ ≤
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
    rw [source_upper_smooth_sum_eq_min_two_mul Q A hQ σ t]
    calc
      _ ≤ (((Q + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
        simpa only [U, R, one_mul] using hFall
      _ ≤ (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by
        exact mul_le_mul_of_nonneg_right hWeight (by positivity)
  rw [typeISourceSmoothBlock_eq_terminal_three_sums Y A r σ t hY
    (by simpa only [Q] using hLower)]
  change ‖(∑ n ∈ Finset.Ioc L (min Q A),
        ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)) -
      (∑ n ∈ Finset.Ioc L (min Q A),
        (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n)) +
      (∑ n ∈ Finset.Ioc Q A,
        (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
          unitaryPhase (logarithmicPhase t n))‖ ≤ _
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc L (min Q A),
          ((n : ℝ) ^ (-σ)) • unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc L (min Q A),
          (typeISmoothStep (2 * (n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ +
        ‖∑ n ∈ Finset.Ioc Q A,
          (typeISmoothStep ((n : ℝ) / Q) * (n : ℝ) ^ (-σ)) •
            unitaryPhase (logarithmicPhase t n)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) +
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) +
        (((L + 1 : ℕ) : ℝ)) ^ (-σ) * (30 * R) := by linarith
    _ = 90 * ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
        Real.sqrt (8 * (((2 ^ r * Y + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ)) := by
      dsimp only [L, Q, R]
      ring

/-- Physical form of the preceding source-block Weyl estimate.  The source
length is kept as the actual natural `Q = 2^r Y`, and the identity
`Q^tau = T` is used only at the final exponent conversion. -/
theorem norm_typeISourceSmoothBlock_le_physical_weyl
    {Y A r : ℕ} {σ T t tau : ℝ}
    (hY : 0 < Y) (hr : 2 ≤ r)
    (hInterior : 2 * (2 ^ r * Y) ≤ A)
    (hσ : 0 ≤ σ) (hσUpper : σ ≤ 1)
    (hT : 1 ≤ T) (htOne : 1 ≤ t) (htUpper : t ≤ 3 * T)
    (htau : 0 < tau)
    (hScale : (((2 ^ r * Y : ℕ) : ℝ)) ^ tau = T)
    (hSquare : ((((2 ^ r * Y) + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t)
    (hCube : t ≤ ((((2 ^ r * Y) / 2 + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      (180 * Real.sqrt 48) *
        T ^ ((1 / 2 - σ) / tau + 1 / 6) := by
  let Q : ℕ := 2 ^ r * Y
  have hQFour : 4 ≤ Q := by
    have hPow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    dsimp only [Q]
    exact hPow.trans (Nat.le_mul_of_pos_right _ hY)
  have hQPos : (0 : ℝ) < Q := by positivity
  have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hHalfCast : ((Q / 2 : ℕ) : ℝ) = (Q : ℝ) / 2 := by
    have hTwice : 2 * (Q / 2) = Q := Nat.mul_div_cancel' hEven
    have hTwiceReal : (2 : ℝ) * (Q / 2 : ℕ) = Q := by exact_mod_cast hTwice
    linarith
  have hHalfPos : (0 : ℝ) < Q / 2 := by positivity
  have hWeight : (((Q / 2 + 1 : ℕ) : ℝ)) ^ (-σ) ≤
      2 * (Q : ℝ) ^ (-σ) := by
    have hHalfLe : (Q : ℝ) / 2 ≤ ((Q / 2 + 1 : ℕ) : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_one, hHalfCast]
      linarith
    have hAnti : (((Q / 2 + 1 : ℕ) : ℝ)) ^ (-σ) ≤
        ((Q : ℝ) / 2) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hHalfPos hHalfLe (neg_nonpos.mpr hσ)
    have hTwoPow : (2 : ℝ) ^ σ ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hσUpper
    calc
      (((Q / 2 + 1 : ℕ) : ℝ)) ^ (-σ) ≤ ((Q : ℝ) / 2) ^ (-σ) := by
        simpa only [hHalfCast] using hAnti
      _ = (2 : ℝ) ^ σ * (Q : ℝ) ^ (-σ) := by
        rw [Real.div_rpow hQPos.le (by norm_num : (0 : ℝ) ≤ 2)]
        rw [Real.rpow_neg (by norm_num : (2 : ℝ) ≥ 0)]
        field_simp [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) σ]
      _ ≤ 2 * (Q : ℝ) ^ (-σ) := by gcongr
  have hQSucc : (((Q + 1 : ℕ) : ℝ)) ≤ 2 * Q := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have htThird : t ^ (1 / 3 : ℝ) ≤ 3 * T ^ (1 / 3 : ℝ) := by
    have hPow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ t) htUpper
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    calc
      t ^ (1 / 3 : ℝ) ≤ (3 * T) ^ (1 / 3 : ℝ) := hPow
      _ = 3 ^ (1 / 3 : ℝ) * T ^ (1 / 3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTPos.le]
      _ ≤ 3 * T ^ (1 / 3 : ℝ) := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
            (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hInside : 8 * (((Q + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ) ≤
      48 * (Q : ℝ) * T ^ (1 / 3 : ℝ) := by
    calc
      8 * (((Q + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ) ≤
          8 * (2 * (Q : ℝ)) * (3 * T ^ (1 / 3 : ℝ)) := by gcongr
      _ = 48 * (Q : ℝ) * T ^ (1 / 3 : ℝ) := by ring
  have hSqrt := Real.sqrt_le_sqrt hInside
  have hSqrtRewrite :
      Real.sqrt (48 * (Q : ℝ) * T ^ (1 / 3 : ℝ)) =
        Real.sqrt 48 * (Q : ℝ) ^ (1 / 2 : ℝ) * T ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 48 * (Q : ℝ)),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 48)]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    congr 1
    rw [← Real.rpow_mul hTPos.le]
    congr 1
    ring
  have hQPower : (Q : ℝ) ^ (1 / 2 - σ) =
      T ^ ((1 / 2 - σ) / tau) := by
    rw [← hScale, ← Real.rpow_mul hQPos.le]
    congr 1
    field_simp [htau.ne']
  have hRaw := norm_typeISourceSmoothBlock_le_weyl
    hY hr hInterior hσ htOne hSquare hCube
  calc
    ‖typeISourceSmoothBlock Y A r σ t‖ ≤
        90 * (((Q / 2 + 1 : ℕ) : ℝ) ^ (-σ)) *
          Real.sqrt (8 * (((Q + 1 : ℕ) : ℝ)) * t ^ (1 / 3 : ℝ)) := by
      simpa only [Q] using hRaw
    _ ≤ 90 * (2 * (Q : ℝ) ^ (-σ)) *
          Real.sqrt (48 * (Q : ℝ) * T ^ (1 / 3 : ℝ)) := by gcongr
    _ = (180 * Real.sqrt 48) *
          (((Q : ℝ) ^ (-σ) * (Q : ℝ) ^ (1 / 2 : ℝ)) *
            T ^ (1 / 6 : ℝ)) := by
      rw [hSqrtRewrite]
      ring
    _ = (180 * Real.sqrt 48) *
          ((Q : ℝ) ^ (1 / 2 - σ) * T ^ (1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hQPos]
      congr 3
      ring
    _ = (180 * Real.sqrt 48) *
          T ^ ((1 / 2 - σ) / tau + 1 / 6) := by
      rw [hQPower, Real.rpow_add hTPos]

/-- Uniform physical side conditions for the complete source-block Weyl
estimate.  The factor eight in the quadratic condition is exactly what
absorbs the left displacement of the slab at the boundary `tau = 2`; the
cubic condition uses the fixed positive gap between `tauMax` and `3`. -/
theorem eventually_source_weyl_geometry
    {d tauMax : ℝ} (hTauMaxTwo : 2 ≤ tauMax)
    (hTauMaxThree : tauMax < 3) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T t tau : ℝ} {Q : ℕ}, T₀ ≤ T → 1 < Q → 2 ∣ Q →
        2 ≤ tau → tau ≤ tauMax → (Q : ℝ) ^ tau = T →
        T ^ d ≤ T / 2 → T - T ^ d ≤ t → t ≤ 2 * T + T ^ d →
        (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t ∧
          t ≤ ((((Q / 2) + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
  let rho : ℝ := 3 / tauMax - 1
  have hTauMaxPos : 0 < tauMax := by linarith
  have hRho : 0 < rho := by
    dsimp only [rho]
    rw [sub_pos, one_lt_div hTauMaxPos]
    exact hTauMaxThree
  have hTop := tendsto_rpow_atTop hRho
  have hEventually := (tendsto_atTop.1 hTop) 24
  rw [eventually_atTop] at hEventually
  obtain ⟨Tpow, hTpow⟩ := hEventually
  let T₀ := max 8 Tpow
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T t tau Q hT hQ hEven hTauTwo hTauUpper hScale hDisp htLower htUpper
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hTauPos : 0 < tau := by linarith
  have hQPos : (0 : ℝ) < Q := by positivity
  have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast hQ.le
  have htHalf : T / 2 ≤ t := by linarith
  have htThree : t ≤ 3 * T := by linarith
  have hQSquare : (Q : ℝ) ^ (2 : ℕ) ≤ T := by
    calc
      (Q : ℝ) ^ (2 : ℕ) = (Q : ℝ) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (Q : ℝ) 2).symm
      _ ≤ (Q : ℝ) ^ tau :=
        Real.rpow_le_rpow_of_exponent_le hQOne hTauTwo
      _ = T := hScale
  have hSucc : (((Q + 1 : ℕ) : ℝ)) ≤ 2 * Q := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hQuadratic : (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 8 * t := by
    calc
      (((Q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ (2 * (Q : ℝ)) ^ (2 : ℕ) := by
        gcongr
      _ = 4 * (Q : ℝ) ^ (2 : ℕ) := by ring
      _ ≤ 4 * T := by gcongr
      _ ≤ 8 * t := by linarith
  have hInv : 3 / tauMax ≤ 3 / tau := by
    exact div_le_div_of_nonneg_left (by norm_num) hTauPos hTauUpper
  have hExp : rho ≤ (3 - tau) / tau := by
    dsimp only [rho]
    rw [sub_div]
    field_simp [hTauPos.ne']
    nlinarith [hInv]
  have hPowerSaving : 24 ≤ (Q : ℝ) ^ (3 - tau) := by
    calc
      (24 : ℝ) ≤ T ^ rho := hTpow T hTPow
      _ ≤ T ^ ((3 - tau) / tau) :=
        Real.rpow_le_rpow_of_exponent_le hTOne hExp
      _ = (Q : ℝ) ^ (3 - tau) := by
        rw [← hScale, ← Real.rpow_mul hQPos.le]
        congr 1
        field_simp [hTauPos.ne']
  have hQCube : 24 * T ≤ (Q : ℝ) ^ (3 : ℕ) := by
    calc
      24 * T = 24 * (Q : ℝ) ^ tau := by rw [hScale]
      _ ≤ (Q : ℝ) ^ (3 - tau) * (Q : ℝ) ^ tau := by
        exact mul_le_mul_of_nonneg_right hPowerSaving
          (Real.rpow_nonneg hQPos.le _)
      _ = (Q : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_add hQPos]
        convert Real.rpow_natCast (Q : ℝ) 3 using 1
        all_goals ring_nf
  have hHalfCast : ((Q / 2 : ℕ) : ℝ) = (Q : ℝ) / 2 := by
    have hTwice : 2 * (Q / 2) = Q := Nat.mul_div_cancel' hEven
    have hTwiceReal : (2 : ℝ) * (Q / 2 : ℕ) = Q := by exact_mod_cast hTwice
    linarith
  refine ⟨hQuadratic, ?_⟩
  calc
    t ≤ 3 * T := htThree
    _ ≤ ((Q : ℝ) / 2) ^ (3 : ℕ) := by
      rw [show ((Q : ℝ) / 2) ^ (3 : ℕ) = (Q : ℝ) ^ (3 : ℕ) / 8 by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith
    _ = ((Q / 2 : ℕ) : ℝ) ^ (3 : ℕ) := by rw [hHalfCast]
    _ ≤ (((Q / 2 + 1 : ℕ) : ℝ)) ^ (3 : ℕ) := by
      gcongr
      norm_num

/-- The complementary physical source-scale alternative is empty.  This
consumes a nonempty source family and its actual pointwise lower bound; the
`Nat.clog` loss is supplied explicitly and absorbed by the displayed
positive exponent budget. -/
theorem eventually_source_far_family_impossible
    {sigma d u q v Clog : ℝ}
    (hsigmaUpper : sigma < 1)
    (hq : 0 < q) (hTauMaxTwo : 2 ≤ 6 * sigma - 3 - q)
    (hBudget : u + v < q / 18) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T tau : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        2 * (2 ^ r * Y) ≤ A →
        tau = typeILogarithmicScale T (2 ^ r * Y) →
        2 ≤ tau → tau < 6 * sigma - 3 - q →
        T ^ d ≤ T / 2 →
        W.Nonempty →
        (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
        (((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤ Clog * T ^ v) →
        (∀ t ∈ W,
          ((3 / 4) * (T ^ (-u) / 2)) /
              (Nat.clog 2 A + 1 : ℕ) ≤
            ‖typeISourceSmoothBlock Y A r sigma t‖) →
        False := by
  let tauMax : ℝ := 6 * sigma - 3 - q
  have hTauMaxTwo' : 2 ≤ tauMax := by simpa only [tauMax] using hTauMaxTwo
  have hTauMaxThree : tauMax < 3 := by dsimp only [tauMax]; linarith
  obtain ⟨Tgeo, hTgeo, hGeo⟩ :=
    eventually_source_weyl_geometry hTauMaxTwo' hTauMaxThree
  have hSaving : 0 < q / 18 - u - v := by linarith
  let Cw : ℝ := 180 * Real.sqrt 48
  have hCw : 0 < Cw := by dsimp only [Cw]; positivity
  have hTop := tendsto_rpow_atTop hSaving
  have hEventually := (tendsto_atTop.1 hTop)
    ((8 / 3 : ℝ) * Clog * Cw + 1)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tconst, hTconst⟩ := hEventually
  let T₀ : ℝ := max Tgeo Tconst
  refine ⟨T₀, hTgeo.trans (le_max_left _ _), ?_⟩
  intro T tau Y A r W hT hA hY hr hInterior hTau hTauTwo hFar hDisp
    hW hRange hLog hLarge
  have hTGeo : Tgeo ≤ T := (le_max_left _ _).trans hT
  have hTEight : 8 ≤ T := hTgeo.trans hTGeo
  have hTConst : Tconst ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hTauPos : 0 < tau := by linarith
  have hTauUpper : tau ≤ tauMax := by dsimp only [tauMax]; linarith
  obtain ⟨t, ht⟩ := hW
  let Q : ℕ := 2 ^ r * Y
  have hQFour : 4 ≤ Q := by
    have hPow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    dsimp only [Q]
    exact hPow.trans (Nat.le_mul_of_pos_right _ hY)
  have hQOne : 1 < Q := by omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hScale : (Q : ℝ) ^ tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have htLower : T / 2 ≤ t := by linarith [(hRange t ht).1]
  have htOne : 1 ≤ t := by linarith
  have htUpper : t ≤ 3 * T := by linarith [(hRange t ht).2]
  obtain ⟨hSquare, hCube⟩ := hGeo hTGeo hQOne hEven hTauTwo
    hTauUpper hScale hDisp (hRange t ht).1 (hRange t ht).2
  have hWeyl := norm_typeISourceSmoothBlock_le_physical_weyl
    hY hr hInterior (by linarith : 0 ≤ sigma) hsigmaUpper.le hTOne
    htOne htUpper hTauPos hScale hSquare hCube
  let F : ℝ := (1 / 2 - sigma) / tau + 1 / 6
  have hExp : F ≤ -q / 18 := by
    have hCore : F < -q / (6 * tau) := by
      dsimp only [F]
      rw [lt_div_iff₀ (mul_pos (by norm_num) hTauPos)]
      field_simp [hTauPos.ne']
      linarith
    have hUniform : -q / (6 * tau) ≤ -q / 18 := by
      have hDiv : q / 18 ≤ q / (6 * tau) := by
        exact div_le_div_of_nonneg_left hq.le (by positivity) (by linarith)
      simpa only [neg_div] using (neg_le_neg hDiv)
    exact hCore.le.trans hUniform
  have hPow : T ^ F ≤ T ^ (-q / 18) :=
    Real.rpow_le_rpow_of_exponent_le hTOne hExp
  have hNorm : ‖typeISourceSmoothBlock Y A r sigma t‖ ≤
      Cw * T ^ (-q / 18) := by
    exact hWeyl.trans (mul_le_mul_of_nonneg_left
      (by simpa only [F] using hPow) hCw.le)
  have hLogPos : (0 : ℝ) < ((Nat.clog 2 A + 1 : ℕ) : ℝ) := by positivity
  have hLower : (3 / 4 : ℝ) * (T ^ (-u) / 2) ≤
      ((Nat.clog 2 A + 1 : ℕ) : ℝ) *
        ‖typeISourceSmoothBlock Y A r sigma t‖ := by
    simpa only [mul_comm] using (div_le_iff₀ hLogPos).mp (hLarge t ht)
  have hLogNonneg : 0 ≤ Clog * T ^ v := hLogPos.le.trans hLog
  have hThreshold : (3 / 8 : ℝ) * T ^ (-u) ≤
      (Clog * Cw) * T ^ (v - q / 18) := by
    calc
      (3 / 8 : ℝ) * T ^ (-u) =
          (3 / 4) * (T ^ (-u) / 2) := by ring
      _ ≤ ((Nat.clog 2 A + 1 : ℕ) : ℝ) *
          ‖typeISourceSmoothBlock Y A r sigma t‖ := hLower
      _ ≤ (Clog * T ^ v) * (Cw * T ^ (-q / 18)) := by
        exact mul_le_mul hLog hNorm (norm_nonneg _) hLogNonneg
      _ = (Clog * Cw) * (T ^ v * T ^ (-q / 18)) := by ring
      _ = (Clog * Cw) * T ^ (v - q / 18) := by
        rw [← Real.rpow_add hTPos]
        ring_nf
  have hConstRaw := hTconst T hTConst
  change (8 / 3 : ℝ) * Clog * Cw + 1 ≤
    T ^ (q / 18 - u - v) at hConstRaw
  have hConst : (8 / 3 : ℝ) * Clog * Cw <
      T ^ (q / 18 - u - v) := (lt_add_one _).trans_le hConstRaw
  have hScaled := mul_lt_mul_of_pos_right hConst
    (Real.rpow_pos_of_pos hTPos (v - q / 18))
  have hIdentity : T ^ (q / 18 - u - v) * T ^ (v - q / 18) =
      T ^ (-u) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hContradiction : (Clog * Cw) * T ^ (v - q / 18) <
      (3 / 8 : ℝ) * T ^ (-u) := by
    calc
      (Clog * Cw) * T ^ (v - q / 18) =
          (3 / 8 : ℝ) * (((8 / 3 : ℝ) * Clog * Cw) *
            T ^ (v - q / 18)) := by ring
      _ < (3 / 8 : ℝ) *
          (T ^ (q / 18 - u - v) * T ^ (v - q / 18)) := by
        exact mul_lt_mul_of_pos_left hScaled (by norm_num)
      _ = (3 / 8 : ℝ) * T ^ (-u) := by rw [hIdentity]
  linarith

set_option maxHeartbeats 1200000

/-- A genuinely large interior source block must lie on the stationary side
of the B-process margin.  This is proved from the sharp-support square-root
bound above; the margin is not added as a hypothesis to the final consumer. -/
theorem eventually_large_source_forces_complementary_margin
    {σ d u : ℝ} (hσOne : σ < 1)
    (hd : 0 < d) (hdOne : d < 1)
    (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T t τ : ℝ) (Y A r : ℕ), T₀ ≤ T →
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        2 * (2 ^ r * Y) ≤ A →
        T - T ^ d ≤ t → t ≤ 2 * T + T ^ d →
        T ^ d ≤ T / 2 →
        τ = typeILogarithmicScale T (2 ^ r * Y) →
        ((3 / 4) * (T ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : ℕ) ≤
          ‖typeISourceSmoothBlock Y A r σ t‖ →
        -100 * d ≤ τ / 2 - σ := by
  let a : ℝ := 2 * σ - 200 * d
  have haOne : 1 < a := by
    dsimp only [a]
    have hScaled : 200 * d ≤ (σ - 1 / 2) / 5 := by
      calc
        200 * d ≤ 200 * ((σ - 1 / 2) / 1000) := by gcongr
        _ = (σ - 1 / 2) / 5 := by ring
    linarith
  have haPos : 0 < a := zero_lt_one.trans haOne
  have haTwo : a < 2 := by dsimp only [a]; linarith
  let δ : ℝ := 2 / a - 1
  have hδ : 0 < δ := by
    dsimp only [δ]
    rw [sub_pos, one_lt_div haPos]
    exact haTwo
  have hPowTop := tendsto_rpow_atTop hδ
  have hEventuallyPow := (tendsto_atTop.1 hPowTop) 48
  rw [eventually_atTop] at hEventuallyPow
  obtain ⟨Tpow, hTpow⟩ := hEventuallyPow
  have hDecay : u + 1 / 2 < σ / a := by
    have hGapEq : σ / a - 1 / 2 = 100 * d / a := by
      field_simp [haPos.ne']
      dsimp only [a]
      ring
    have hFifty : 50 * d < 100 * d / a := by
      rw [lt_div_iff₀ haPos]
      have hMul := mul_lt_mul_of_pos_right haTwo
        (mul_pos (by norm_num : (0 : ℝ) < 50) hd)
      nlinarith
    have huFifty : u < 50 * d := huD.trans_lt (by nlinarith [hd])
    linarith
  have hRatioTop := tendsto_typeI_terminal_ratio (σ / a) (u + 1 / 2) hDecay
  let c : ℝ := 6 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ
  have hc : 0 < c := by dsimp only [c]; positivity
  have hScaled := hRatioTop.const_mul c
  have hEventuallySmall := (tendsto_order.1 hScaled).2 (3 / 8 : ℝ) (by norm_num)
  rw [eventually_atTop] at hEventuallySmall
  obtain ⟨Tsmall, hTsmall⟩ := hEventuallySmall
  obtain ⟨Thalf, hThalf, hHalf⟩ := eventually_rpow_le_half_self d hdOne
  let T₀ : ℝ := max 8 (max Tpow (max Tsmall Thalf))
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T t τ Y A r hT hA hY hr hUpper htLower htUpper hDisp hτ hLarge
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tpow (max Tsmall Thalf) ≤ T := (le_max_right _ _).trans hT
  have hTPow : Tpow ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Tsmall Thalf ≤ T := (le_max_right _ _).trans hRest
  have hTSmall : Tsmall ≤ T := (le_max_left _ _).trans hRest₁
  have hTHalf : Thalf ≤ T := (le_max_right _ _).trans hRest₁
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  by_contra hMargin
  have hτa : τ < a := by
    have : τ / 2 - σ < -100 * d := lt_of_not_ge hMargin
    dsimp only [a]
    linarith
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  have hQFour : 4 ≤ Q := by
    dsimp only [Q]
    have hpow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    calc
      4 = 4 * 1 := by omega
      _ ≤ 4 * Y := Nat.mul_le_mul_left 4 hY
      _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpow
  have hQOne : 1 < Q := by omega
  have hQ : 0 < Q := by omega
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left
      (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  have hL : 0 < L := by omega
  have hScale : (Q : ℝ) ^ τ = T := by
    subst τ
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hTa : T ≤ (Q : ℝ) ^ a := by
    rw [← hScale]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hQOne.le) hτa.le
  have hRoot : T ^ (1 / a) ≤ (Q : ℝ) := by
    have hRaised := Real.rpow_le_rpow hTPos.le hTa
      (by positivity : 0 ≤ 1 / a)
    calc
      T ^ (1 / a) ≤ ((Q : ℝ) ^ a) ^ (1 / a) := hRaised
      _ = (Q : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]
        field_simp [haPos.ne']
        exact Real.rpow_one (Q : ℝ)
  have hPowAt : 48 ≤ T ^ δ := hTpow T hTPow
  have hQSquare : 48 * T ≤ (Q : ℝ) ^ 2 := by
    have hSquare := pow_le_pow_left₀ (Real.rpow_nonneg hTPos.le _) hRoot 2
    have hPowerEq : (T ^ (1 / a)) ^ (2 : ℕ) = T ^ (2 / a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
      congr 1
      ring
    have hSplit : T ^ (2 / a) = T * T ^ δ := by
      rw [show 2 / a = 1 + δ by dsimp only [δ]; ring,
        Real.rpow_add hTPos, Real.rpow_one]
    rw [hPowerEq, hSplit] at hSquare
    nlinarith [mul_le_mul_of_nonneg_left hPowAt hTPos.le]
  have htHalf : T / 2 ≤ t := by linarith
  have htThree : t ≤ 3 * T := by linarith
  have htSq : t ≤ (L : ℝ) ^ 2 := by
    have hLReal : (L : ℝ) = (Q : ℝ) / 2 := by
      have hTwiceLReal : (2 : ℝ) * L = Q := by exact_mod_cast hTwiceL
      linarith
    rw [hLReal]
    nlinarith
  have hNorm := norm_typeISourceSmoothBlock_le_sqrt
    (Y := Y) (A := A) (r := r) (σ := σ) (t := t)
    hY hr (by linarith) (by linarith) (by simpa only [Q, L] using htSq)
  subst A
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hAUpper : (A : ℝ) ≤ 6 * T := by
    dsimp only [A]
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul (by linarith))
  have hQUpper : (Q : ℝ) ≤ 3 * T := by
    have hUpperReal : (2 : ℝ) * Q ≤ A := by exact_mod_cast hUpper
    linarith
  have hSqrt : Real.sqrt t ≤ Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt t ≤ Real.sqrt (3 * T) := Real.sqrt_le_sqrt htThree
      _ = Real.sqrt 3 * Real.sqrt T := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
        congr 1
        exact Real.sqrt_eq_rpow T
  have hRatio : (Q : ℝ) / t ≤ 6 := by
    have hQt : (Q : ℝ) ≤ 6 * t := by linarith only [hQUpper, htHalf]
    exact (div_le_iff₀ (by linarith only [htHalf, hTPos])).2 hQt
  have hSqrtOne : 1 ≤ T ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hTOne (by norm_num)
  have hBracket :
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
        (100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ) := by
    have hRatioTerm : 6 * Real.pi * (Q : ℝ) / t ≤ 36 * Real.pi := by
      calc
        6 * Real.pi * (Q : ℝ) / t = 6 * Real.pi * ((Q : ℝ) / t) := by ring
        _ ≤ 6 * Real.pi * 6 := by gcongr
        _ = 36 * Real.pi := by ring
    calc
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
          100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) + 36 * Real.pi := by
        gcongr
      _ ≤ 100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) +
          36 * Real.pi * T ^ (1 / 2 : ℝ) := by
        have hPiTerm : 36 * Real.pi ≤ 36 * Real.pi * T ^ (1 / 2 : ℝ) := by
          calc
            36 * Real.pi = 36 * Real.pi * 1 := by ring
            _ ≤ 36 * Real.pi * T ^ (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_left hSqrtOne (by positivity)
        exact add_le_add_right hPiTerm _
      _ = (100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ) := by ring
  have hWeightQ : (((L + 1 : ℕ) : ℝ)) ^ (-σ) ≤
      ((Q : ℝ) / 2) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · norm_num only [Nat.cast_add, Nat.cast_one]
      have hLReal : (L : ℝ) = (Q : ℝ) / 2 := by
        have hTwiceLReal : (2 : ℝ) * L = Q := by exact_mod_cast hTwiceL
        linarith
      linarith
    · linarith
  have hWeightT : ((Q : ℝ) / 2) ^ (-σ) ≤
      2 ^ σ * T ^ (-σ / a) := by
    have hQNeg : (Q : ℝ) ^ (-σ) ≤ T ^ (-σ / a) := by
      have hRaised := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hTPos (1 / a))
        hRoot (by linarith : -σ ≤ 0)
      have hEq : (T ^ (1 / a)) ^ (-σ) = T ^ (-σ / a) := by
        rw [← Real.rpow_mul hTPos.le]
        congr 1
        ring
      simpa only [hEq] using hRaised
    rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ Q)
      (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      (Q : ℝ) ^ (-σ) / (2 ^ σ)⁻¹ = 2 ^ σ * (Q : ℝ) ^ (-σ) := by
        field_simp
      _ ≤ 2 ^ σ * T ^ (-σ / a) :=
        mul_le_mul_of_nonneg_left hQNeg (Real.rpow_nonneg (by norm_num) _)
  have hNormBound : ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
        T ^ (1 / 2 - σ / a) := by
    calc
      _ ≤ 3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) := by
        simpa only [Q, L, A] using hNorm
      _ ≤ 3 * (2 ^ σ * T ^ (-σ / a)) *
          ((100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ)) := by
        calc
          3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
              (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) =
            3 * ((((L + 1 : ℕ) : ℝ) ^ (-σ)) *
              (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t)) := by ring
          _ ≤ 3 * ((2 ^ σ * T ^ (-σ / a)) *
              ((100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ))) := by
            have hSourceBracketNonneg :
                0 ≤ 100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t := by
              have htPos : 0 < t := by linarith only [htHalf, hTPos]
              positivity
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul (hWeightQ.trans hWeightT) hBracket
                hSourceBracketNonneg (by positivity)) (by norm_num)
          _ = _ := by ring
      _ = 3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
          T ^ (1 / 2 - σ / a) := by
        calc
          3 * (2 ^ σ * T ^ (-σ / a)) *
              ((100 * Real.sqrt 3 + 36 * Real.pi) * T ^ (1 / 2 : ℝ)) =
            3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
              (T ^ (-σ / a) * T ^ (1 / 2 : ℝ)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hTPos]
            congr 1
            ring_nf
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hClog := sharp_cutoff_clog_le_log_majorant T hTEight
  have hkBound : ((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤
      2 * (1 + (Real.log 6 + Real.log T) / Real.log 2) := by
    have hEnvelopeOne : 1 ≤
        1 + (Real.log 6 + Real.log T) / Real.log 2 := by
      have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hLogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
      have hLogT : 0 ≤ Real.log T := Real.log_nonneg hTOne
      have : 0 ≤ (Real.log 6 + Real.log T) / Real.log 2 :=
        div_nonneg (add_nonneg hLogSix hLogT) hLogTwo.le
      linarith
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hSmallAt :
      c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
          T ^ (u + 1 / 2 - σ / a) < 3 / 8 := by
    simpa only [mul_assoc] using hTsmall T hTSmall
  have hPowerSplit : T ^ (u + 1 / 2 - σ / a) * T ^ (-u) =
      T ^ (1 / 2 - σ / a) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hNumerator :
      ((Nat.clog 2 A + 1 : ℕ) : ℝ) *
          (3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ / a)) <
        (3 / 4) * (T ^ (-u) / 2) := by
    have hMul := mul_lt_mul_of_pos_right hSmallAt
      (Real.rpow_pos_of_pos hTPos (-u))
    calc
      _ ≤ (2 * (1 + (Real.log 6 + Real.log T) / Real.log 2)) *
          (3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ / a)) := by gcongr
      _ = (c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u + 1 / 2 - σ / a)) * T ^ (-u) := by
        rw [show T ^ (1 / 2 - σ / a) =
            T ^ (u + 1 / 2 - σ / a) * T ^ (-u) from hPowerSplit.symm]
        dsimp only [c]
        ring
      _ < (3 / 8) * T ^ (-u) := hMul
      _ = (3 / 4) * (T ^ (-u) / 2) := by ring
  have hkPos : (0 : ℝ) < (Nat.clog 2 A + 1 : ℕ) := by positivity
  have hThresholdLt : ‖typeISourceSmoothBlock Y A r σ t‖ <
      ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ) := by
    rw [lt_div_iff₀ hkPos]
    calc
      ‖typeISourceSmoothBlock Y A r σ t‖ * (Nat.clog 2 A + 1 : ℕ) =
          (Nat.clog 2 A + 1 : ℕ) * ‖typeISourceSmoothBlock Y A r σ t‖ := by ring
      _ ≤ (Nat.clog 2 A + 1 : ℕ) *
          (3 * (100 * Real.sqrt 3 + 36 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ / a)) :=
        mul_le_mul_of_nonneg_left hNormBound hkPos.le
      _ < _ := hNumerator
  exact (not_lt_of_ge (by simpa only [A] using hLarge)) hThresholdLt

/-- Budgeted form of the signed B-process extraction.  The choice of `R`
uses `L¹+1`, so it is valid even if the fixed Mellin mass vanishes; the
strict source gap and the normalization of the reflected polynomial are
then elementary consequences of `R ≥ 2`. -/
theorem exists_signed_shift_large_normalized_reflected_wide_of_budget
    {Y A r M : ℕ} {σ t V H K E : ℝ}
    (hY : 0 < Y)
    (hLower : (((Y + 1 : ℕ) : ℝ)) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (hσ : 0 ≤ σ) (hM : 1 < M)
    (hV : 0 < V) (hH : 0 ≤ H) (hK : 0 < K)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r σ t‖)
    (hZero :
      ‖typeISourceNormalizationScalar σ t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) *
          typeINormalizedFourier σ t 0)‖ ≤ V / 8)
    (hFar :
      ‖typeISourceNormalizationScalar σ t (2 ^ r * Y : ℕ) *
        typeINormalizedFarTail σ t (2 ^ r * Y) M‖ ≤ V / 8)
    (hKernelNeg : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral σ (t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hKernelPos : ∀ u ∈ Set.Icc (-H) H,
      ‖typeIPowerReflectionIntegral σ (-t + u)
        (((2 ^ r * Y : ℕ) : ℝ) / 2)
        (2 * M * (2 ^ r * Y : ℕ))‖ ≤ K)
    (hTailNeg :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial σ t
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral σ (t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hTailPos :
      ‖∫ u : ℝ in (Set.Icc (-H) H)ᶜ,
        typeIReflectedMellinPolynomial σ (-t)
            ((2 ^ r * Y : ℕ) : ℝ) M u *
          typeIDyadicCutoffMellin u *
            typeIPowerReflectionIntegral σ (-t + u)
              (((2 ^ r * Y : ℕ) : ℝ) / 2)
              (2 * M * (2 ^ r * Y : ℕ))‖ ≤ E)
    (hTailBudget : E ≤ Real.pi * V / 8)
    (hR : 2 ≤ (Real.pi * V) /
      (8 * ((2 ^ r * Y : ℕ) : ℝ) * K *
        (typeIDyadicCutoffMellinL1 + 1))) :
    let R := (Real.pi * V) /
      (8 * ((2 ^ r * Y : ℕ) : ℝ) * K *
        (typeIDyadicCutoffMellinL1 + 1))
    let S := R / (2 * (M : ℝ) ^ σ)
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff σ M) (-(t + u))‖) ∨
    (∃ u ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff σ M) (t - u)‖) := by
  dsimp only
  let Q : ℕ := 2 ^ r * Y
  let R : ℝ := (Real.pi * V) /
    (8 * (Q : ℝ) * K * (typeIDyadicCutoffMellinL1 + 1))
  let S : ℝ := R / (2 * (M : ℝ) ^ σ)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hMass : 0 ≤ typeIDyadicCutoffMellinL1 :=
    typeIDyadicCutoffMellinL1_nonneg
  have hDen : 0 < 8 * (Q : ℝ) * K *
      (typeIDyadicCutoffMellinL1 + 1) := by positivity
  have hRPos : 0 < R := by dsimp only [R]; positivity
  have hCentral : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 ≤
      Real.pi * V / 8 := by
    dsimp only [R]
    rw [div_eq_mul_inv]
    have hFrac : typeIDyadicCutoffMellinL1 /
        (typeIDyadicCutoffMellinL1 + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hQV : 0 ≤ Real.pi * V / 8 := by positivity
    field_simp [hDen.ne']
    nlinarith [mul_le_mul_of_nonneg_left hFrac (mul_nonneg Real.pi_pos.le hV.le)]
  have hGap : (Q : ℝ) * R * K * typeIDyadicCutoffMellinL1 + E <
      Real.pi * V / 2 := by
    have hPiV : 0 < Real.pi * V := mul_pos Real.pi_pos hV
    nlinarith
  have hNormalize : S + (M : ℝ) ^ (-σ) ≤ R / (M : ℝ) ^ σ := by
    have hMPow : 0 < (M : ℝ) ^ σ := by positivity
    have hInv : (M : ℝ) ^ (-σ) = 1 / (M : ℝ) ^ σ := by
      simpa only [one_div] using
        (Real.rpow_neg (by positivity : (0 : ℝ) ≤ M) σ)
    have hRAt : 2 ≤ R := by simpa only [R, Q] using hR
    rw [hInv]
    dsimp only [S]
    have hRewrite : R / (2 * (M : ℝ) ^ σ) + 1 / (M : ℝ) ^ σ =
        (R / 2 + 1) / (M : ℝ) ^ σ := by
      field_simp [hMPow.ne']
    rw [hRewrite]
    exact (div_le_div_iff_of_pos_right hMPow).2 (by nlinarith)
  simpa only [Q, R, S] using
    exists_signed_shift_large_normalized_reflected_wide
      hY hLower hUpper hσ hM hV.le hH hRPos.le hLarge hZero hFar
      hKernelNeg hKernelPos hTailNeg hTailPos hGap hNormalize

/-- The terminal three-sum majorant is eventually smaller than the exact
classified-source threshold.  The statement keeps the additional `clog + 1`
selection loss, rather than silently identifying it with the detector's
original `clog`. -/
theorem eventually_terminal_source_majorant_lt_threshold
    {σ u : ℝ} (hσ : 1 / 2 < σ) (hu : u < σ - 1 / 2) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T t : ℝ) (Q L : ℕ), T₀ ≤ T →
      T / 2 ≤ L → (Q : ℝ) ≤ 24 * T →
      T / 2 ≤ t → t ≤ 3 * T →
      3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) <
        ((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) := by
  have hDecay : u + 1 / 2 < σ := by linarith
  have hTendsto := tendsto_typeI_terminal_ratio σ (u + 1 / 2) hDecay
  let c : ℝ := 6 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ
  have hc : 0 < c := by dsimp only [c]; positivity
  have hScaled := hTendsto.const_mul c
  have hEventually := (tendsto_order.1 hScaled).2 (3 / 8 : ℝ) (by norm_num)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tscale, hTscale⟩ := hEventually
  let T₀ := max 8 Tscale
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T t Q L hT hTL hQT htLower htUpper
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTscale' : Tscale ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have htPos : 0 < t := by linarith
  have hLPos : (0 : ℝ) < L + 1 := by positivity
  have hWeight : (((L + 1 : ℕ) : ℝ)) ^ (-σ) ≤ (T / 2) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · norm_num only [Nat.cast_add, Nat.cast_one]
      linarith
    · linarith
  have hSqrt : Real.sqrt t ≤ Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt t ≤ Real.sqrt (3 * T) := Real.sqrt_le_sqrt htUpper
      _ = Real.sqrt 3 * Real.sqrt T := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
        congr 1
        exact Real.sqrt_eq_rpow T
  have hRatio : (Q : ℝ) / t ≤ 48 := by
    rw [div_le_iff₀ htPos]
    nlinarith
  have hSqrtOne : 1 ≤ T ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hRatioTerm : 6 * Real.pi * (Q : ℝ) / t ≤ 6 * Real.pi * 48 := by
    calc
      6 * Real.pi * (Q : ℝ) / t = 6 * Real.pi * ((Q : ℝ) / t) := by ring
      _ ≤ 6 * Real.pi * 48 := mul_le_mul_of_nonneg_left hRatio
        (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hBracket :
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
        (100 * Real.sqrt 3 + 288 * Real.pi) * T ^ (1 / 2 : ℝ) := by
    calc
      100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t ≤
          100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) +
            6 * Real.pi * 48 := add_le_add (mul_le_mul_of_nonneg_left hSqrt
              (by norm_num)) hRatioTerm
      _ ≤ 100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ)) +
            (6 * Real.pi * 48) * T ^ (1 / 2 : ℝ) := by
        have hCoeff : 0 ≤ 6 * Real.pi * 48 := by positivity
        have hScaledRatio := mul_le_mul_of_nonneg_left hSqrtOne hCoeff
        have hRatioLift : 6 * Real.pi * 48 ≤
            (6 * Real.pi * 48) * T ^ (1 / 2 : ℝ) := by
          simpa only [mul_one] using hScaledRatio
        linarith
      _ = (100 * Real.sqrt 3 + 288 * Real.pi) * T ^ (1 / 2 : ℝ) := by ring
  have hDivPow : (T / 2) ^ (-σ) = 2 ^ σ * T ^ (-σ) := by
    rw [Real.div_rpow hTPos.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hPowCombine : T ^ (-σ) * T ^ (1 / 2 : ℝ) =
      T ^ (1 / 2 - σ) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hMajorant :
      3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
          (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) ≤
        3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
          T ^ (1 / 2 - σ) := by
    calc
      _ ≤ 3 * (T / 2) ^ (-σ) *
          ((100 * Real.sqrt 3 + 288 * Real.pi) * T ^ (1 / 2 : ℝ)) := by
        gcongr
      _ = 3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
          T ^ (1 / 2 - σ) := by
        rw [hDivPow, ← hPowCombine]
        ring
  let A := ⌊sharpZetaCutoff T⌋₊
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hkPos : 0 < (Nat.clog 2 A + 1 : ℕ) := by omega
  have hkRealPos : (0 : ℝ) < (Nat.clog 2 A + 1 : ℕ) := by exact_mod_cast hkPos
  have hClog := sharp_cutoff_clog_le_log_majorant T hTEight
  have hEnvelopeOne : 1 ≤
      1 + (Real.log 6 + Real.log T) / Real.log 2 := by
    have hLogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hLogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hFrac : 0 ≤ (Real.log 6 + Real.log T) / Real.log 2 := by positivity
    linarith
  have hkBound : (Nat.clog 2 A + 1 : ℕ) ≤
      2 * (1 + (Real.log 6 + Real.log T) / Real.log 2) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hRatioAt := hTscale T hTscale'
  have hRatioSmall :
      c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
          T ^ (u + 1 / 2 - σ) < 3 / 8 := by
    simpa only [mul_assoc] using hRatioAt
  have hPowSplit : T ^ (u + 1 / 2 - σ) * T ^ (-u) =
      T ^ (1 / 2 - σ) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hNumerator :
      (Nat.clog 2 A + 1 : ℕ) *
          (3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ)) <
        (3 / 4) * (T ^ (-u) / 2) := by
    have hMul := mul_lt_mul_of_pos_right hRatioSmall
      (Real.rpow_pos_of_pos hTPos (-u))
    calc
      (Nat.clog 2 A + 1 : ℕ) *
          (3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ)) ≤
        (2 * (1 + (Real.log 6 + Real.log T) / Real.log 2)) *
          (3 * (100 * Real.sqrt 3 + 288 * Real.pi) * 2 ^ σ *
            T ^ (1 / 2 - σ)) := by gcongr
      _ = (c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u + 1 / 2 - σ)) * T ^ (-u) := by
        calc
          _ = c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
              T ^ (1 / 2 - σ) := by dsimp only [c]; ring
          _ = c * (1 + (Real.log 6 + Real.log T) / Real.log 2) *
              (T ^ (u + 1 / 2 - σ) * T ^ (-u)) := by rw [hPowSplit]
          _ = _ := by ring
      _ < (3 / 8) * T ^ (-u) := hMul
      _ = (3 / 4) * (T ^ (-u) / 2) := by ring
  change 3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
      (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) <
    ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ)
  rw [lt_div_iff₀ hkRealPos]
  exact (mul_le_mul_of_nonneg_right hMajorant (Nat.cast_nonneg _)).trans_lt
    (by simpa only [mul_comm] using hNumerator)

/-- The upper-edge alternative returned by the actual common-source
selection is empty for all sufficiently large heights.  Its scale comparison
is derived from a nonzero dyadic coefficient of that same source block. -/
theorem eventually_no_terminal_classified_source
    {σ d u : ℝ} (hσ : 1 / 2 < σ) (hu : u < σ - 1 / 2) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T : ℝ) (Y A r : ℕ) (W : Finset ℝ), T₀ ≤ T →
      A = ⌊sharpZetaCutoff T⌋₊ →
      0 < Y → 2 ≤ r → A < 2 * (2 ^ r * Y) →
      W.Nonempty → IsSeparated 1 W →
      (∀ t ∈ W,
        ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ) ≤
          ‖typeISourceSmoothBlock Y A r σ t‖) →
      (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
      T ^ d ≤ T / 2 → False := by
  obtain ⟨Tterminal, hTterminal, hTerminalSmall⟩ :=
    eventually_terminal_source_majorant_lt_threshold hσ hu
  let T₀ := max Tterminal 12
  have hEightTwelve : (8 : ℝ) ≤ 12 := by norm_num
  refine ⟨T₀, hEightTwelve.trans (le_max_right _ _), ?_⟩
  intro T Y A r W hT hA hY hr hTerminal hW hSep hLarge hRange hDisp
  have hTTerminal : Tterminal ≤ T := (le_max_left _ _).trans hT
  have hTTwelve : 12 ≤ T := (le_max_right _ _).trans hT
  have hTEight : 8 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  subst A
  let A : ℕ := ⌊sharpZetaCutoff T⌋₊
  let Q : ℕ := 2 ^ r * Y
  let L : ℕ := Q / 2
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hV : 0 < ((3 / 4) * (T ^ (-u) / 2)) /
      (Nat.clog 2 A + 1 : ℕ) := by positivity
  obtain ⟨j, hj, W', _hWsub, _hSep', _hCard, _hLarge', _hPUpper, hQFourP⟩ :=
    extract_normalized_source_dyadic_block W hY hAOne hV hW hSep hLarge
  have hPA : 2 ^ j ≤ A := by
    have hjClog : j < Nat.clog 2 (A + 1) := Finset.mem_range.mp hj
    have hpow : 2 ^ j < A + 1 := Nat.pow_lt_of_lt_clog hjClog
    omega
  have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hAUpper : (A : ℝ) ≤ 6 * T := by
    dsimp only [A]
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul (by linarith))
  have hQUpperNat : Q < 4 * A := by
    dsimp only [Q] at hQFourP ⊢
    exact hQFourP.trans_le (Nat.mul_le_mul_left 4 hPA)
  have hQUpper : (Q : ℝ) ≤ 24 * T := by
    calc
      (Q : ℝ) ≤ 4 * A := by exact_mod_cast hQUpperNat.le
      _ ≤ 24 * T := by nlinarith
  have hEven : 2 ∣ Q := by
    dsimp only [Q]
    exact dvd_mul_of_dvd_left (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwiceL : 2 * L = Q := by
    dsimp only [L]
    exact Nat.mul_div_cancel' hEven
  obtain ⟨t, htW⟩ := hW
  have hCutLt : sharpZetaCutoff T < (A : ℝ) + 1 := by
    dsimp only [A]
    exact_mod_cast Nat.lt_floor_add_one (sharpZetaCutoff T)
  have hFourTA : 4 * T < (A : ℝ) + 1 :=
    (four_mul_lt_sharpZetaCutoff T).trans hCutLt
  have hAQT : (A : ℝ) + 1 ≤ 2 * Q := by
    have hNat : A + 1 ≤ 2 * Q := by
      dsimp only [Q] at hTerminal ⊢
      omega
    exact_mod_cast hNat
  have hTL : T / 2 ≤ (L : ℝ) := by
    have hQL : (Q : ℝ) = 2 * L := by exact_mod_cast hTwiceL.symm
    rw [hQL] at hAQT
    nlinarith
  have htLower : T / 2 ≤ t := by
    have := (hRange t htW).1
    linarith
  have htUpper : t ≤ 3 * T := by
    have := (hRange t htW).2
    linarith
  have hLThree : (3 : ℝ) ≤ L := by nlinarith
  have htSq : t ≤ (L : ℝ) ^ 2 := by
    have : 3 * T ≤ (L : ℝ) ^ 2 := by nlinarith [sq_nonneg ((L : ℝ) - T / 2)]
    exact htUpper.trans this
  have hBound := norm_typeISourceSmoothBlock_terminal_le
    (Y := Y) (A := A) (r := r) (σ := σ) (t := t) hY hr
    (by simpa only [Q] using hTerminal) (by linarith) (by linarith) (by
      simpa only [L, Q] using htSq)
  have hSmall := hTerminalSmall T t Q L hTTerminal hTL hQUpper
    htLower htUpper
  have hLargeAt := hLarge t htW
  have hThresholdEq :
      ((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) =
        ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ) := by
    rfl
  rw [hThresholdEq] at hSmall
  have hBound' : ‖typeISourceSmoothBlock Y A r σ t‖ ≤
      3 * (((L + 1 : ℕ) : ℝ) ^ (-σ)) *
        (100 * Real.sqrt t + 6 * Real.pi * (Q : ℝ) / t) := by
    simpa only [L, Q] using hBound
  linarith

/-- The two bottom source blocks selected from the long tail have a physical
logarithmic scale comparable with `1 / d`.  Both comparisons retain the
literal natural floor and the factor `2 ^ r`; no real surrogate for the
source length is introduced. -/
theorem eventually_lower_source_logarithmic_scale_bounds
    (d : ℝ) (hd : 0 < d) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ (T : ℝ) (r : ℕ), T₀ ≤ T → r < 2 →
      let Y := ⌊T ^ d⌋₊
      let N := 2 ^ r * Y
      1 < N ∧ 1 / (2 * d) ≤ typeILogarithmicScale T N ∧
        typeILogarithmicScale T N ≤ 2 / d := by
  obtain ⟨Tupper, hTupper, hUpper⟩ :=
    eventually_typeI_logarithmic_scale_upper d hd
  let T₀ : ℝ := max Tupper ((2 : ℝ) ^ (1 / d))
  refine ⟨T₀, hTupper.trans (le_max_left _ _), ?_⟩
  intro T r hT hr
  dsimp only
  have hTUpper : Tupper ≤ T := (le_max_left _ _).trans hT
  have hTConst : (2 : ℝ) ^ (1 / d) ≤ T :=
    (le_max_right _ _).trans hT
  have hTTwo : 2 ≤ T := hTupper.trans hTUpper
  have hTPos : 0 < T := by linarith
  let Y := ⌊T ^ d⌋₊
  let N := 2 ^ r * Y
  have hUpperAt := hUpper T r hTUpper
  dsimp only at hUpperAt
  rcases hUpperAt with ⟨hNOne, hTauUpper⟩
  have hPowTwo : 2 ≤ T ^ d := by
    have hRaised := Real.rpow_le_rpow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      hTConst hd.le
    have hCancel : ((2 : ℝ) ^ (1 / d)) ^ d = 2 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hExp : 1 / d * d = 1 := by field_simp [hd.ne']
      rw [hExp, Real.rpow_one]
    simpa only [hCancel] using hRaised
  have hYUpper : (Y : ℝ) ≤ T ^ d := by
    dsimp only [Y]
    exact Nat.floor_le (Real.rpow_nonneg hTPos.le _)
  have hPowR : 2 ^ r ≤ 2 := by
    have hrCases : r = 0 ∨ r = 1 := by omega
    rcases hrCases with rfl | rfl <;> norm_num
  have hNUpper : (N : ℝ) ≤ T ^ (2 * d) := by
    have hFirst : (N : ℝ) ≤ 2 * T ^ d := by
      calc
        (N : ℝ) = (2 ^ r : ℕ) * (Y : ℝ) := by
          dsimp only [N]
          push_cast
          rfl
        _ ≤ 2 * (Y : ℝ) := by
          gcongr
          exact_mod_cast hPowR
        _ ≤ 2 * T ^ d := by gcongr
    have hSecond : 2 * T ^ d ≤ T ^ d * T ^ d := by
      nlinarith [Real.rpow_nonneg hTPos.le d]
    calc
      (N : ℝ) ≤ 2 * T ^ d := hFirst
      _ ≤ T ^ d * T ^ d := hSecond
      _ = T ^ (2 * d) := by
        rw [← Real.rpow_add hTPos]
        congr 1
        ring
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hNOne)
  have hLowerPhysical : (N : ℝ) ^ (1 / (2 * d)) ≤ T := by
    have hExp : 0 ≤ 1 / (2 * d) := by positivity
    have hRaised := Real.rpow_le_rpow hNPos.le hNUpper hExp
    calc
      (N : ℝ) ^ (1 / (2 * d)) ≤
          (T ^ (2 * d)) ^ (1 / (2 * d)) := hRaised
      _ = T := by
        rw [← Real.rpow_mul hTPos.le]
        have hCancel : 2 * d * (1 / (2 * d)) = 1 := by
          field_simp [hd.ne']
        rw [hCancel, Real.rpow_one]
  have hTauLower : 1 / (2 * d) ≤ typeILogarithmicScale T N :=
    (Real.le_logb_iff_rpow_le (by exact_mod_cast hNOne) hTPos).mpr
      hLowerPhysical
  exact ⟨hNOne, hTauLower, hTauUpper⟩

-- Generated closures: source context is replayed in the next part.
end GuthMaynard.NativeMoment
end
