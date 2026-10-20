module
public import GuthMaynard.Improvement.RadialDecay

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GuthMaynard.Improvement

def logModulated (a : ℝ → ℂ) (s x : ℝ) : ℂ :=
  a x * Complex.exp ((s:ℂ)*Complex.I*(Real.log x:ℂ))

theorem logModulated_smoothOn {a : ℝ → ℂ}
    (ha : ContDiffOn ℝ ∞ a (Ioi 0)) (s : ℝ) :
    ContDiffOn ℝ ∞ (logModulated a s) (Ioi 0) := by
  apply ha.mul
  apply ContDiffOn.cexp
  apply contDiffOn_const.mul
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    (Real.contDiffOn_log.mono (fun x hx => ne_of_gt hx))

theorem logModulated_deriv {a : ℝ → ℂ}
    (ha : ContDiffOn ℝ ∞ a (Ioi 0)) (s : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (logModulated a s) x =
      logModulated (deriv a) s x + (s:ℂ)*Complex.I*logModulated (fun x => a x/(x:ℂ)) s x := by
  have hd : HasDerivAt a (deriv a x) x :=
    ((ha.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have he := (((Real.hasDerivAt_log hx.ne').ofReal_comp).const_mul ((s:ℂ)*Complex.I)).cexp
  have hh := (hd.mul he).deriv
  change deriv (logModulated a s) x = _ at hh
  rw [hh]
  unfold logModulated
  push_cast
  ring

/-- Derivatives of the actual logarithmically modulated amplitude have
polynomial time growth. The constant precedes every real time parameter. -/
theorem logModulated_uniform_deriv (n : ℕ) {l u : ℝ} (hl : 0 < l)
    (a : ℝ → ℂ) (ha : ContDiffOn ℝ ∞ a (Ioi 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, ∀ x ∈ Icc l u,
      ‖iteratedDeriv n (logModulated a s) x‖ ≤ C*(1+|s|)^n := by
  induction n generalizing a with
  | zero =>
    obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (ha.continuousOn.mono (fun x hx => lt_of_lt_of_le hl hx.1))
    refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
    intro s x hx
    have he : ‖Complex.exp ((s:ℂ)*Complex.I*(Real.log x:ℂ))‖ = 1 := by
      rw [show (s:ℂ)*Complex.I*(Real.log x:ℂ) = ((s*Real.log x:ℝ):ℂ)*Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    simpa [logModulated,he] using (hC x hx).trans (le_max_right 1 C)
  | succ n ih =>
    have had : ContDiffOn ℝ ∞ (deriv a) (Ioi 0) := ha.deriv_of_isOpen isOpen_Ioi (by simp)
    have haq : ContDiffOn ℝ ∞ (fun x => a x/(x:ℂ)) (Ioi 0) := by
      have hi : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) (Ioi 0) :=
        contDiffOn_id.inv (fun x hx => ne_of_gt hx)
      simpa [div_eq_mul_inv] using ha.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hi)
    obtain ⟨C,hC,hc⟩ := ih (deriv a) had
    obtain ⟨D,hD,hd⟩ := ih (fun x => a x/(x:ℂ)) haq
    refine ⟨C+D,by positivity,?_⟩
    intro s x hx
    have hxp : x ∈ Ioi (0:ℝ) := lt_of_lt_of_le hl hx.1
    have heq : deriv (logModulated a s) =ᶠ[𝓝 x]
        (fun z => logModulated (deriv a) s z + (s:ℂ)*Complex.I*logModulated (fun z => a z/(z:ℂ)) s z) := by
      filter_upwards [isOpen_Ioi.mem_nhds hxp] with z hz
      exact logModulated_deriv ha s hz
    have hdc := ((logModulated_smoothOn had s).contDiffAt (isOpen_Ioi.mem_nhds hxp)).of_le (show (n:ℕ∞ω) ≤ ∞ by simp)
    have hqc := ((logModulated_smoothOn haq s).contDiffAt (isOpen_Ioi.mem_nhds hxp)).of_le (show (n:ℕ∞ω) ≤ ∞ by simp)
    rw [iteratedDeriv_succ',heq.iteratedDeriv_eq n,
      iteratedDeriv_fun_add hdc ((contDiffAt_const : ContDiffAt ℝ n (fun _ : ℝ => (s:ℂ)*Complex.I) x).mul hqc),iteratedDeriv_const_mul _ hqc]
    calc
      _ ≤ ‖iteratedDeriv n (logModulated (deriv a) s) x‖ +
          ‖(s:ℂ)*Complex.I*iteratedDeriv n (logModulated (fun z => a z/(z:ℂ)) s) x‖ := norm_add_le _ _
      _ ≤ C*(1+|s|)^n + |s| *(D*(1+|s|)^n) := by
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
        gcongr
        · exact hc s x hx
        · exact hd s x hx
      _ ≤ (C+D)*(1+|s|)^(n+1) := by
        rw [pow_succ]
        nlinarith [mul_nonneg (mul_nonneg hC.le (abs_nonneg s)) (pow_nonneg (by positivity : 0 ≤ 1+|s|) n),
          mul_nonneg hD.le (pow_nonneg (by positivity : 0 ≤ 1+|s|) n)]

/-- A cutoff supported away from zero removes the logarithm's singularity. -/
theorem logModulated_smooth {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hs : ∀ x, x ∉ Icc l u → a x = 0) (s : ℝ) :
    ContDiff ℝ ∞ (logModulated a s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · exact (logModulated_smoothOn ha.contDiffOn s).contDiffAt (isOpen_Ioi.mem_nhds hx)
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0:ℂ)) x).congr_of_eventuallyEq
    have hxl : x < l := lt_of_le_of_lt (le_of_not_gt hx) hl
    filter_upwards [isOpen_Iio.mem_nhds hxl] with z hz
    have haz := hs z (fun h => (not_lt_of_ge h.1) hz)
    simp [logModulated,haz]

/-- A global uniform derivative bound for the genuine compact cutoff. -/
theorem logModulated_global_deriv {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hs : ∀ x, x ∉ Icc l u → a x = 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s x : ℝ,
      ‖iteratedDeriv n (logModulated a s) x‖ ≤ C*(1+|s|)^n := by
  obtain ⟨C,hC,hb⟩ := logModulated_uniform_deriv n (u := u) hl a ha.contDiffOn
  refine ⟨C,hC,?_⟩
  intro s x
  by_cases hx : x ∈ Icc l u
  · exact hb s x hx
  · have hz : ∀ z, z ∉ Icc l u → logModulated a s z = 0 := by
      intro z hz; simp [logModulated,hs z hz]
    rw [iteratedDeriv_zero_off_interval hz n hx,norm_zero]
    positivity

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.logModulated_smoothOn
#print axioms GuthMaynard.Improvement.logModulated_deriv
#print axioms GuthMaynard.Improvement.logModulated_uniform_deriv

#print axioms GuthMaynard.Improvement.logModulated_smooth
#print axioms GuthMaynard.Improvement.logModulated_global_deriv
