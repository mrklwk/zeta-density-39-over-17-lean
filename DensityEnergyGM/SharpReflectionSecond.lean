module
public import DensityEnergyGM.RealScaleSecondMoment
public import DensityEnergyGM.FiveTermEnergyUniform
public import DensityEnergyGM.EnergyCenteredReflection

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

theorem norm_gmR_translateSet (c : ℝ) (W : Finset ℝ) {r : ℝ} (hr : 0 < r) :
    ‖gmR (translateSet c W) r‖ = ‖gmR W r‖ := by
  rw [native_ratio_sum_eq_phase _ hr, native_ratio_sum_eq_phase _ hr]
  have hsum : (∑ t ∈ translateSet c W, phase r t) =
      (∑ t ∈ W, phase r t) * star (phase r c) := by
    unfold translateSet
    rw [sum_image (by intro x hx y hy h; change x-c=y-c at h; linarith), sum_mul]
    exact sum_congr rfl (fun t _ => (phase_time_difference r t c).symm)
  rw [hsum, norm_mul, norm_star]
  have hunit : ‖phase r c‖ = 1 := by
    rw [← exponentialPhase_log, exponentialPhase_norm]
  rw [hunit, mul_one]

theorem finiteRatioSecond_translateSet (A : Finset ℕ)
    (hA : ∀ n ∈ A, 0 < n) (c : ℝ) (W : Finset ℝ) :
    finiteRatioSecond A (translateSet c W) = finiteRatioSecond A W := by
  unfold finiteRatioSecond
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro m hm
  rw [norm_gmR_translateSet c W (div_pos
    (by exact_mod_cast hA n hn) (by exact_mod_cast hA m hm))]

/-- The already proved sharp all-pairs second moment, uniform at every
real height>=2 and arbitrary interval translate. A fixed dilation B in
the short-scale restriction is paid only in the upfront constant. -/
theorem real_scale_ratio_second_sharp_uniform_translate (ε B : ℝ)
    (hε : 0 < ε) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ M : ℝ, 2 ≤ T → 0 < M → M^2 ≤ B*T →
      ∀ W : Finset ℝ, IsSeparated 1 W →
        (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
        finiteRatioSecond (sourceRatioIndices M) W ≤ C*T^ε*
          (M^2*(discreteAdditiveEnergy W:ℝ)^(1/2:ℝ)+
            (W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)*
              (M^(9/5:ℝ)+T^(1/4:ℝ)*M^(6/5:ℝ))) := by
  obtain ⟨C,T₀,hC,hT₀,hBound⟩ := real_scale_ratio_second_sharp_native ε hε
  let D : ℝ := max B (max 1 (T₀/2))
  have hBD : B ≤ D := le_max_left _ _
  have hD1 : 1 ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hTD : T₀/2 ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hD : 0 < D := by linarith
  let q : ℝ := D^(1/4:ℝ)
  have hq : 1 ≤ q := Real.one_le_rpow hD1 (by norm_num)
  refine ⟨C*D^ε*q,by positivity,?_⟩
  intro T t₀ M hT hM hMB W hSep hW
  have hTp : 0 < T := by linarith
  have hHeight : T₀ ≤ D*T := by nlinarith
  have hScale : M^2 ≤ D*T := hMB.trans (mul_le_mul_of_nonneg_right hBD hTp.le)
  have hBase : InBaseInterval (D*T) (translateSet t₀ W) := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
    obtain ⟨hl,hh⟩ := hW u hu
    have hDT : T ≤ D*T := le_mul_of_one_le_left hTp.le hD1
    exact ⟨by linarith,by linarith⟩
  have h := hBound M (D*T) (translateSet t₀ W) hM hHeight hScale
    (isSeparated_translate 1 t₀ W hSep) hBase
  have hA : ∀ n ∈ sourceRatioIndices M, 0 < n := by
    intro n hn
    exact Nat.zero_lt_of_lt (mem_Ioc.mp hn).1
  rw [finiteRatioSecond_translateSet _ hA, translateSet_card,
    discrete_energy_translateSet] at h
  rw [Real.mul_rpow hD.le hTp.le, Real.mul_rpow hD.le hTp.le] at h
  let U := M^2*(discreteAdditiveEnergy W:ℝ)^(1/2:ℝ)+
    (W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)*M^(9/5:ℝ)
  let V := (W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)*
    T^(1/4:ℝ)*M^(6/5:ℝ)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hBudget : U+q*V ≤ q*(U+V) := by nlinarith [mul_nonneg (by linarith : 0 ≤ q-1) hU]
  have h' : finiteRatioSecond (sourceRatioIndices M) W ≤
      (C*D^ε*T^ε)*(U+q*V) := by
    convert h using 1
    dsimp [U,V,q]
    ring
  have hm := h'.trans (mul_le_mul_of_nonneg_left hBudget (by positivity : 0 ≤ C*D^ε*T^ε))
  exact hm.trans_eq (by dsimp [U,V]; ring)


/-- The reflected dyadic polynomial differs from the positive-frequency sum
only by a common unit phase; the complete W x W energy is unchanged. -/
theorem completePairEnergy_eq_phase_difference {M : ℕ} (hM : 0 < M) (W : Finset ℝ) :
    MathCollab.Density.completePairEnergy M W =
      ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ Ico M (2*M), phase n (t-u)‖^2 := by
  have hNorm (v : ℝ) : ‖MathCollab.Density.dyadicPolynomial M v‖ =
      ‖∑ n ∈ Ico M (2*M), phase n v‖ := by
    have hEq : MathCollab.Density.dyadicPolynomial M v =
        (∑ n ∈ Ico M (2*M), phase n v)*star (phase M v) := by
      unfold MathCollab.Density.dyadicPolynomial
      rw [sum_mul]
      apply sum_congr rfl
      intro n hn
      rw [density_phase_eq,phase_frequency_ratio
        (by exact_mod_cast hM.trans_le (mem_Ico.mp hn).1) (by exact_mod_cast hM)]
    rw [hEq,norm_mul,norm_star]
    have hUnit : ‖phase M v‖=1 := by rw [← exponentialPhase_log,exponentialPhase_norm]
    rw [hUnit,mul_one]
  unfold MathCollab.Density.completePairEnergy
  simp_rw [hNorm]

/-- Every reflected half-open integer block is bounded by the full sharp
real-scale ratio moment, with its exact half-unit endpoint shift. -/
theorem completePairEnergy_le_half_shift_second {M : ℕ} (hM : 0 < M) (W : Finset ℝ) :
    MathCollab.Density.completePairEnergy M W ≤
      finiteRatioSecond (sourceRatioIndices ((M:ℝ)-1/2)) W := by
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hX : 0 < (M:ℝ)-1/2 := by linarith
  have hA : ∀ n ∈ Ico M (2*M), 0<n := fun n hn => hM.trans_le (mem_Ico.mp hn).1
  have hSubset : Ico M (2*M) ⊆ sourceRatioIndices ((M:ℝ)-1/2) := by
    intro n hn
    have hl : (M:ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    have hu : (n:ℝ)+1 ≤ 2*(M:ℝ) := by exact_mod_cast (mem_Ico.mp hn).2
    exact (sourceRatioIndices_mem hX.le n).mpr ⟨by linarith,by linarith⟩
  rw [completePairEnergy_eq_phase_difference hM]
  have h := dirichlet_difference_energy_le (Ico M (2*M)) hA W (fun _ => 1) (by simp)
  simp only [one_mul] at h
  apply h.trans
  have he : (∑ n ∈ Ico M (2*M), ∑ m ∈ Ico M (2*M),
      ‖∑ t ∈ W, phase ((n:ℝ)/m) t‖^2) = finiteRatioSecond (Ico M (2*M)) W := by
    unfold finiteRatioSecond
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [native_ratio_sum_eq_phase W (div_pos
      (by exact_mod_cast hA n hn) (by exact_mod_cast hA m hm))]
  rw [he]
  exact finiteRatioSecond_mono hSubset W

/-- The sharp reflected complete-pair energy at all heights and translates.
No polynomial, moment, support or energy estimate remains as a premise. -/
theorem reflection_complete_pair_energy_sharp {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ,0 < C ∧ ∀ T t₀ : ℝ,2 ≤ T → ∀ M : ℕ,0<M → (M:ℝ) ≤ 4*Real.sqrt T →
      ∀ W : Finset ℝ,(∀ t ∈ W,t ∈ Set.Icc t₀ (t₀+T)) →
        (∀ t ∈ W,∀ u ∈ W,t≠u → 1≤|t-u|) →
        MathCollab.Density.completePairEnergy M W ≤ C*T^η*
          ((M:ℝ)^2*(discreteAdditiveEnergy W:ℝ)^(1/2:ℝ)+
            (W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)*
              ((M:ℝ)^(9/5:ℝ)+T^(1/4:ℝ)*(M:ℝ)^(6/5:ℝ))) := by
  obtain ⟨C,hC,hBound⟩ := real_scale_ratio_second_sharp_uniform_translate η 16 hη (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T t₀ hT M hM hMc W hW hSep
  have hM1 : (1:ℝ)≤M := by exact_mod_cast hM
  have hX : 0<(M:ℝ)-1/2 := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hSq := pow_le_pow_left₀ (Nat.cast_nonneg M) hMc 2
  have hSqRoot := Real.sq_sqrt hT0
  have hMscale : (M:ℝ)^2 ≤ 16*T := by nlinarith
  have hXscale : ((M:ℝ)-1/2)^2 ≤ 16*T :=
    (pow_le_pow_left₀ hX.le (by linarith : (M:ℝ)-1/2≤M) 2).trans hMscale
  have hs : IsSeparated 1 W := by
    intro t ht u hu htu
    simpa only [Real.dist_eq] using hSep t ht u hu htu
  have h := hBound T t₀ ((M:ℝ)-1/2) hT hX hXscale W hs hW
  apply (completePairEnergy_le_half_shift_second hM W).trans (h.trans ?_)
  gcongr <;> linarith

end Montgomery.RationalMoment
