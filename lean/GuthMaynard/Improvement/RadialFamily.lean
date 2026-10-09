module
public import Mathlib

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff SchwartzMap
namespace GuthMaynard.Improvement

/-- Joint continuity of every radial derivative is preserved under products. -/
theorem family_product_deriv_continuous {P : Type*} [TopologicalSpace P]
    (f g : P → ℝ → ℂ) (hf : ∀ p, ContDiff ℝ ∞ (f p)) (hg : ∀ p, ContDiff ℝ ∞ (g p))
    (hfc : ∀ n : ℕ, Continuous (fun z : P × ℝ => iteratedDeriv n (f z.1) z.2))
    (hgc : ∀ n : ℕ, Continuous (fun z : P × ℝ => iteratedDeriv n (g z.1) z.2)) (n : ℕ) :
    Continuous (fun z : P × ℝ => iteratedDeriv n (fun r => f z.1 r*g z.1 r) z.2) := by
  have hid : (fun z : P × ℝ => iteratedDeriv n (fun r => f z.1 r*g z.1 r) z.2) =
      (fun z => ∑ i ∈ Finset.range (n+1), (n.choose i:ℂ)*iteratedDeriv i (f z.1) z.2*iteratedDeriv (n-i) (g z.1) z.2) := by
    funext z
    exact iteratedDeriv_fun_mul ((hf z.1).of_le (by simp)).contDiffAt ((hg z.1).of_le (by simp)).contDiffAt
  rw [hid]
  exact continuous_finsetSum _ (fun i _ => (continuous_const.mul (hfc i)).mul (hgc (n-i)))

def radialAmplitude (a : ℝ → ℂ) (v y r : ℝ) : ℂ :=
  a (v*r)*a (y*r)*((r:ℂ)^2*a r)

theorem radialAmplitude_smooth {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (v y : ℝ) :
    ContDiff ℝ ∞ (radialAmplitude a v y) := by
  have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff
  unfold radialAmplitude
  fun_prop

/-- The actual cutoff r^2*a(rv)*a(ry)*a(r) has jointly continuous radial
derivatives, before any compact ratio parameters are selected. -/
theorem radialAmplitude_deriv_continuous {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (n : ℕ) :
    Continuous (fun z : (ℝ × ℝ) × ℝ => iteratedDeriv n (radialAmplitude a z.1.1 z.1.2) z.2) := by
  let f : (ℝ × ℝ) → ℝ → ℂ := fun p r => a (p.1*r)
  let g : (ℝ × ℝ) → ℝ → ℂ := fun p r => a (p.2*r)
  let b : (ℝ × ℝ) → ℝ → ℂ := fun _ r => (r:ℂ)^2*a r
  have hf : ∀ p, ContDiff ℝ ∞ (f p) := by intro p; dsimp [f]; fun_prop
  have hg : ∀ p, ContDiff ℝ ∞ (g p) := by intro p; dsimp [g]; fun_prop
  have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff
  have hb : ∀ p, ContDiff ℝ ∞ (b p) := by intro p; exact hc.pow 2 |>.mul ha
  have hfc : ∀ n : ℕ, Continuous (fun z : (ℝ × ℝ) × ℝ => iteratedDeriv n (f z.1) z.2) := by
    intro n
    have hid : (fun z : (ℝ × ℝ) × ℝ => iteratedDeriv n (f z.1) z.2) =
        (fun z => z.1.1^n • iteratedDeriv n a (z.1.1*z.2)) := by
      funext z
      exact congrFun (iteratedDeriv_comp_const_smul (ha.of_le (by simp)) z.1.1) z.2
    rw [hid]
    exact (continuous_fst.fst.pow n).smul ((ha.continuous_iteratedDeriv n (by simp)).comp (continuous_fst.fst.mul continuous_snd))
  have hgc : ∀ n : ℕ, Continuous (fun z : (ℝ × ℝ) × ℝ => iteratedDeriv n (g z.1) z.2) := by
    intro n
    have hid : (fun z : (ℝ × ℝ) × ℝ => iteratedDeriv n (g z.1) z.2) =
        (fun z => z.1.2^n • iteratedDeriv n a (z.1.2*z.2)) := by
      funext z
      exact congrFun (iteratedDeriv_comp_const_smul (ha.of_le (by simp)) z.1.2) z.2
    rw [hid]
    exact (continuous_fst.snd.pow n).smul ((ha.continuous_iteratedDeriv n (by simp)).comp (continuous_fst.snd.mul continuous_snd))
  have hbc : ∀ n : ℕ, Continuous (fun z : (ℝ × ℝ) × ℝ => iteratedDeriv n (b z.1) z.2) := by
    intro n
    exact ((hb (0,0)).continuous_iteratedDeriv n (by simp)).comp continuous_snd
  exact family_product_deriv_continuous (fun p r => f p r*g p r) b
    (fun p => (hf p).mul (hg p)) hb (family_product_deriv_continuous f g hf hg hfc hgc) hbc n

/-- Every derivative vanishes off the same fixed closed support interval. -/
theorem iteratedDeriv_zero_off_interval {f : ℝ → ℂ} {l u : ℝ}
    (hs : ∀ r, r ∉ Icc l u → f r = 0) (n : ℕ) {r : ℝ} (hr : r ∉ Icc l u) :
    iteratedDeriv n f r = 0 := by
  have hts : tsupport f ⊆ Icc l u := closure_minimal
    (by intro x hx; by_contra hn; exact hx (hs x hn)) isClosed_Icc
  have hn : r ∉ Function.support (iteratedFDeriv ℝ n f) := fun hx => hr (hts (support_iteratedFDeriv_subset n hx))
  rw [iteratedDeriv_eq_iteratedFDeriv,Function.notMem_support.mp hn]
  rfl

/-- One bound for every ratio pair in a fixed compact box, chosen before
v,y,r. No parameter-dependent seminorm is used as the uniform constant. -/
theorem radialAmplitude_uniform_deriv {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v ∈ Icc v₀ v₁, ∀ y ∈ Icc y₀ y₁, ∀ r : ℝ,
      ‖iteratedDeriv n (radialAmplitude a v y) r‖ ≤ C := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn
    (radialAmplitude_deriv_continuous ha n).continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro v hv y hy r
  by_cases hr : r ∈ Icc l u
  · exact (hC ((v,y),r) ⟨⟨hv,hy⟩,hr⟩).trans (le_max_right _ _)
  · have hz : ∀ x, x ∉ Icc l u → radialAmplitude a v y x = 0 := by
      intro x hx
      simp [radialAmplitude,hs x hx]
    rw [iteratedDeriv_zero_off_interval hz n hr,norm_zero]
    exact le_trans zero_le_one (le_max_left _ _)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.family_product_deriv_continuous
#print axioms GuthMaynard.Improvement.radialAmplitude_smooth
#print axioms GuthMaynard.Improvement.radialAmplitude_deriv_continuous
#print axioms GuthMaynard.Improvement.iteratedDeriv_zero_off_interval
#print axioms GuthMaynard.Improvement.radialAmplitude_uniform_deriv
