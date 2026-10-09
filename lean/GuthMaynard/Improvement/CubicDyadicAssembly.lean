import GuthMaynard.Improvement.CubicDyadicCover
import GuthMaynard.Improvement.CubicModeSymmetry
import GuthMaynard.Improvement.CubicScaleClosure
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Each actual dyadic fiber lies in its literal signed shell box. -/
theorem cubic_dyadic_fiber_box {U : ℝ} (S : Finset (ℤ × (ℤ × ℤ)))
    (hS : ∀ m ∈ S, m.1 ∈ poissonModes U ∧ m.2.1 ∈ poissonModes U ∧ m.2.2 ∈ poissonModes U)
    (k : ℕ × (ℕ × ℕ)) :
    ∀ m ∈ S.filter (fun m => cubicDyadicClass m = k),
      InSignedCubicBox ((2:ℝ)^k.1) ((2:ℝ)^k.2.1) ((2:ℝ)^k.2.2) m := by
  intro m hm
  obtain ⟨hm,hk⟩ := Finset.mem_filter.mp hm
  obtain ⟨h₁,h₂,h₃⟩ := hS m hm
  have hb₁ := integer_dyadic_bounds ((mem_poissonModes U m.1).mp h₁).1
  have hb₂ := integer_dyadic_bounds ((mem_poissonModes U m.2.1).mp h₂).1
  have hb₃ := integer_dyadic_bounds ((mem_poissonModes U m.2.2).mp h₃).1
  have hk₁ : integerDyadicIndex m.1 = k.1 := congrArg Prod.fst hk
  have hk₂ : integerDyadicIndex m.2.1 = k.2.1 := congrArg (fun x => x.2.1) hk
  have hk₃ : integerDyadicIndex m.2.2 = k.2.2 := congrArg (fun x => x.2.2) hk
  rw [hk₁] at hb₁
  rw [hk₂] at hb₂
  rw [hk₃] at hb₃
  exact ⟨hb₁.1,hb₁.2.le,hb₂.1,hb₂.2.le,hb₃.1,hb₃.2.le⟩

/-- Nonempty retained fibers have all three shell parameters at most the
actual real truncation scale U. No enlarged or mask-dependent cover. -/
theorem cubic_dyadic_fiber_scales {U : ℝ} (S : Finset (ℤ × (ℤ × ℤ)))
    (hS : ∀ m ∈ S, m.1 ∈ poissonModes U ∧ m.2.1 ∈ poissonModes U ∧ m.2.2 ∈ poissonModes U)
    (k : ℕ × (ℕ × ℕ)) (hne : (S.filter (fun m => cubicDyadicClass m = k)).Nonempty) :
    (2:ℝ)^k.1 ≤ U ∧ (2:ℝ)^k.2.1 ≤ U ∧ (2:ℝ)^k.2.2 ≤ U := by
  obtain ⟨m,hm⟩ := hne
  have hb := cubic_dyadic_fiber_box S hS k m hm
  obtain ⟨h₁,h₂,h₃⟩ := hS m (Finset.mem_filter.mp hm).1
  exact ⟨hb.1.trans ((mem_poissonModes U m.1).mp h₁).2,
    hb.2.2.1.trans ((mem_poissonModes U m.2.1).mp h₂).2,
    hb.2.2.2.2.1.trans ((mem_poissonModes U m.2.2).mp h₃).2⟩

/-- Uniform sufficient width conditions for every denominator shell. -/
theorem cubic_dyadic_width {a c T L H U K : ℝ} (_ha : 0 < a)
    (hL : 0 < L) (hH : 0 < H) (hK : 1 ≤ K) (hKU : K ≤ U)
    (_hT : 0 ≤ T)
    (h1 : max 1 (1/a)*(H/L) ≤ 1)
    (hc : max 1 (1/a)*(H/L) ≤ c/4)
    (hbudget : L*U ≤ max 1 (1/a)*H*T) :
    max 1 (1/a)*(H/(L*K)) ≤ 1 ∧
      max 1 (1/a)*(H/(L*K)) ≤ c/4 ∧
      (max 1 (1/a)*(H/(L*K)))⁻¹ ≤ T := by
  have hq : 0 < max 1 (1/a) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK0 : 0 < K := by linarith
  have hw : 0 < max 1 (1/a)*(H/(L*K)) := by positivity
  have hle : max 1 (1/a)*(H/(L*K)) ≤ max 1 (1/a)*(H/L) := by
    apply mul_le_mul_of_nonneg_left _ hq.le
    apply div_le_div_of_nonneg_left hH.le hL
    nlinarith
  refine ⟨hle.trans h1,hle.trans hc,?_⟩
  apply (inv_le_iff_one_le_mul₀ hw).mpr
  have he : T*(max 1 (1/a)*(H/(L*K))) = (max 1 (1/a)*H*T)/(L*K) := by ring
  rw [he]
  exact (le_div_iff₀ (mul_pos hL hK0)).mpr (by nlinarith)

/-- Actual complete finite strip sum over retained nonzero modes. Both
integrability and the uniform bound follow from the proved signed boxes;
no energy estimate or mask-dependent multiplicity is assumed. -/
theorem cubic_dyadic_strip_assembly (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T U L H : ℝ) (r₀ r : ℝ → ℝ)
      (A₀ : Set ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ U → U ≤ T^4 → 0 < L → 0 < H →
      max 1 (1/a)*(H/L) ≤ 1 → max 1 (1/a)*(H/L) ≤ c/4 →
      L*U ≤ max 1 (1/a)*H*T →
      MeasurableSet A₀ → Measurable r₀ → MemLp r₀ 2 → (∀ v, 0 ≤ r₀ v) →
      Measurable r → Integrable (fun x => r x^2) → Integrable (fun x => r x^4) →
      (∀ x, 0 ≤ r x) → (∀ x, x ∉ Icc c d → r x = 0) →
      (∀ m ∈ S, m.1 ∈ poissonModes U ∧ m.2.1 ∈ poissonModes U ∧ m.2.2 ∈ poissonModes U) →
      IntegrableOn (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) (Icc a b) ∧
      (∫ v in Icc a b, A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) ≤
        C*((cubicDyadicClasses U).card:ℝ)*(H/L)*
          Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b))*Real.sqrt (T^ε)*
          (U^2*(∫ x, r x^2)+U*Real.sqrt (∫ x, r x^4)) := by
  obtain ⟨C,hC,hbox⟩ := signed_cubic_mixed_box a b c d ha hab hc hcd hε
  refine ⟨C,hC,?_⟩
  intro T U L H r₀ r A₀ S hT hU hUT hL hH hw1 hwc hbudget hA hr₀ hmem₀ hr₀0 hr hr2 hr4 hr0 hs hS
  let F (k : ℕ × (ℕ × ℕ)) (v : ℝ) :=
    A₀.indicator r₀ v * ∑ m ∈ S.filter (fun m => cubicDyadicClass m = k), cubicStripMass r L H m v
  let Z := C*(H/L)*Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b))*
    Real.sqrt (T^ε)*(U^2*(∫ x, r x^2)+U*Real.sqrt (∫ x, r x^4))
  have hM : 0 ≤ ∫ x, r x^2 := integral_nonneg (fun x => sq_nonneg _)
  have hE : 0 ≤ ∫ x, r x^4 := integral_nonneg (fun x => pow_nonneg (hr0 x) _)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hTp : 0 < T := by linarith
  have hTε : 0 ≤ T^ε := Real.rpow_nonneg hTp.le _
  have hf : ∀ k, IntegrableOn (F k) (Icc a b) ∧ (∫ v in Icc a b, F k v) ≤ Z := by
    intro k
    by_cases hn : (S.filter (fun m => cubicDyadicClass m = k)).Nonempty
    · obtain ⟨hBU,hKU,hDU⟩ := cubic_dyadic_fiber_scales S hS k hn
      have hB : 1 ≤ (2:ℝ)^k.1 := one_le_pow₀ (by norm_num)
      have hK : 1 ≤ (2:ℝ)^k.2.1 := one_le_pow₀ (by norm_num)
      have hD : 1 ≤ (2:ℝ)^k.2.2 := one_le_pow₀ (by norm_num)
      have hKp : 0 < (2:ℝ)^k.2.1 := by positivity
      obtain ⟨hw₁,hw₂,hw₃⟩ := cubic_dyadic_width ha hL hH hK hKU hTp.le hw1 hwc hbudget
      obtain ⟨hInt,hbound⟩ := hbox T U ((2:ℝ)^k.2.1) ((2:ℝ)^k.1) ((2:ℝ)^k.2.2) L H
        r₀ r A₀ (S.filter (fun m => cubicDyadicClass m = k)) hT hK hKU hB hBU hD hDU hUT
        hL hH hw₁ hw₂ hw₃ hA hr₀ hmem₀ hr₀0 hr hr2 hr4 hr0 hs (cubic_dyadic_fiber_box S hS k)
      refine ⟨hInt,hbound.trans ?_⟩
      rw [Real.sqrt_mul hTε]
      calc
        _ ≤ C*(H/(L*(2:ℝ)^k.2.1))*Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b))*
            (Real.sqrt (T^ε)*((2:ℝ)^k.2.1*(U^2*(∫ x, r x^2)+U*Real.sqrt (∫ x, r x^4)))) := by
          gcongr
          exact cubic_shell_sqrt_normalization hK hKU hM hE
        _ = Z := by dsimp [Z]; field_simp
    · have he : S.filter (fun m => cubicDyadicClass m = k) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hf0 : F k = 0 := by funext v; simp [F,he]
      rw [hf0]
      exact ⟨integrableOn_zero,by simpa using hZ⟩
  have he (v : ℝ) : (∑ k ∈ cubicDyadicClasses U, F k v) =
      A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v := by
    unfold F
    rw [← Finset.mul_sum,cubic_dyadic_sum_partition hU S _ hS]
  have hInt : IntegrableOn (fun v => ∑ k ∈ cubicDyadicClasses U, F k v) (Icc a b) :=
    integrable_finsetSum _ (fun k _ => (hf k).1)
  refine ⟨by simpa only [he] using hInt,?_⟩
  simp_rw [← he]
  rw [integral_finsetSum _ (fun k _ => (hf k).1)]
  calc
    _ ≤ ∑ _k ∈ cubicDyadicClasses U, Z := Finset.sum_le_sum (fun k _ => (hf k).2)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [Z]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.cubic_dyadic_fiber_box
#print axioms GuthMaynard.Improvement.cubic_dyadic_fiber_scales
#print axioms GuthMaynard.Improvement.cubic_dyadic_width

#print axioms GuthMaynard.Improvement.cubic_dyadic_strip_assembly
