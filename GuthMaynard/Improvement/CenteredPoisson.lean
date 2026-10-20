module
public import GuthMaynard.Improvement.LogPoissonTail
public import GuthMaynard.Improvement.RetainedCubicKernel

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap
namespace GuthMaynard.Improvement

/-- The full centered kernel is defined from its literal finite discrete
sum and continuous term, independently of any Poisson expansion. -/
def centeredKernel (a : ℝ → ℂ) (l u L s : ℝ) : ℂ :=
  (∑ d ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, logModulated a s ((d:ℝ)/L)) -
    (L:ℂ)*∫ x, logModulated a s x

theorem logModulated_scaled_schwartz {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u L : ℝ} (hl : 0 < l) (hL : 0 < L)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (s : ℝ) :
    ∃ ψ : 𝓢(ℝ,ℂ), (ψ : ℝ → ℂ) = fun x => logModulated a s (x/L) := by
  have hd : ContDiff ℝ ∞ (fun x => logModulated a s (x/L)) :=
    (logModulated_smooth ha hl hs s).comp (contDiff_id.div_const L)
  have hc : HasCompactSupport (fun x => logModulated a s (x/L)) := by
    apply HasCompactSupport.intro (K := Icc (l*L) (u*L)) isCompact_Icc
    intro x hx
    have hn : x/L ∉ Icc l u := by
      intro h
      exact hx ⟨(le_div_iff₀ hL).mp h.1,(div_le_iff₀ hL).mp h.2⟩
    simp [logModulated,hs (x/L) hn]
  exact ⟨hc.toSchwartzMap hd,rfl⟩

/-- Actual scaled Poisson formula, with all smoothness/decay premises
discharged by the given fixed cutoff. -/
theorem logModulated_poisson {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u L : ℝ} (hl : 0 < l) (hL : 0 < L)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (s : ℝ) :
    (∑ d ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, logModulated a s ((d:ℝ)/L)) =
      (L:ℂ)*∑' m : ℤ, 𝓕 (logModulated a s) (L*(m:ℝ)) := by
  obtain ⟨ψ,hψ⟩ := logModulated_scaled_schwartz ha hl hL hs s
  have hp := ψ.tsum_eq_tsum_fourier 0
  have hz : scaledModulated (logModulated a s) L 0 = (ψ:ℝ→ℂ) := by
    rw [hψ]
    funext x
    simp [scaledModulated,phase]
  have hf : ∀ m : ℤ, 𝓕 ψ m = (L:ℂ)*𝓕 (logModulated a s) (L*(m:ℝ)) := by
    intro m
    rw [SchwartzMap.fourier_coe,← hz,fourier_scaledModulated _ hL]
    simp [Complex.real_smul]
  simp only [zero_add] at hp
  simp only [hf] at hp
  simp at hp
  rw [tsum_mul_left] at hp
  rw [← hp]
  rw [tsum_eq_sum (s := Finset.Icc ⌈l*L⌉ ⌊u*L⌋)]
  · apply Finset.sum_congr rfl
    intro d _
    exact congrFun hψ d |>.symm
  · intro d hd
    rw [hψ]
    have hn : (d:ℝ)/L ∉ Icc l u := by
      intro h
      apply hd
      rw [Finset.mem_Icc]
      exact ⟨Int.ceil_le.mpr ((le_div_iff₀ hL).mp h.1),Int.le_floor.mpr ((div_le_iff₀ hL).mp h.2)⟩
    simp [logModulated,hs _ hn]

/-- The zero-threshold tail is exactly the nonzero-mode sum. -/
theorem poissonRemainder_zero (f : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (m : ℤ) :
    poissonRemainder f L 0 0 m = if m = 0 then 0 else 𝓕 f (L*(m:ℝ)) := by
  by_cases hm : m = 0
  · subst m; simp [poissonRemainder]
  · simp [poissonRemainder,hm,hL.ne']

/-- Absolute convergence of the actual nonzero Poisson series. -/
theorem logModulated_nonzero_summable {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u L : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hL : 0 < L)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (s : ℝ) :
    Summable (fun m : ℤ => ‖if m = 0 then 0 else 𝓕 (logModulated a s) (L*(m:ℝ))‖) := by
  obtain ⟨C,hC,h⟩ := logModulated_poisson_tail ha hl hlu hs 0
  simpa only [poissonRemainder_zero _ hL] using (h s L 0 0 hL le_rfl).1

/-- The literal centered finite kernel equals the absolutely convergent
nonzero Poisson series. No operator trace identity is built into this claim. -/
theorem centeredKernel_poisson {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u L : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hL : 0 < L)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (s : ℝ) :
    centeredKernel a l u L s =
      (L:ℂ)*∑' m : ℤ, if m = 0 then 0 else 𝓕 (logModulated a s) (L*(m:ℝ)) := by
  let f : ℤ → ℂ := fun m => 𝓕 (logModulated a s) (L*(m:ℝ))
  have hn : Summable (fun m : ℤ => if m = 0 then 0 else f m) :=
    (logModulated_nonzero_summable ha hl hlu hL hs s).of_norm
  have hz : Summable (fun m : ℤ => if m = 0 then f 0 else 0) := (hasSum_ite_eq 0 (f 0)).summable
  have hf : Summable f := (hn.add hz).congr (fun m => by by_cases h : m = 0 <;> simp [h])
  have he := hf.tsum_eq_add_tsum_ite 0
  have hzero : f 0 = ∫ x, logModulated a s x := by
    simp [f,fourier_eq_phase_integral,phase]
  unfold centeredKernel
  rw [logModulated_poisson ha hl hL hs s]
  change (L:ℂ)*(∑' m, f m) - (L:ℂ)*(∫ x, logModulated a s x) = _
  rw [he,hzero,mul_add,add_sub_cancel_left]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.logModulated_scaled_schwartz
#print axioms GuthMaynard.Improvement.logModulated_poisson

#print axioms GuthMaynard.Improvement.poissonRemainder_zero
#print axioms GuthMaynard.Improvement.logModulated_nonzero_summable
#print axioms GuthMaynard.Improvement.centeredKernel_poisson
