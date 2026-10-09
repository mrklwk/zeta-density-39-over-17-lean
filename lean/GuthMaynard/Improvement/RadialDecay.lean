module
public import GuthMaynard.Improvement.RadialFamily
public import GuthMaynard.Improvement.PoissonReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

/-- Compact support gives genuine integrability of every radial derivative. -/
theorem compact_iteratedDeriv_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {l u : ℝ} (hs : ∀ x, x ∉ Icc l u → f x = 0) (n : ℕ) : Integrable (iteratedDeriv n f) := by
  exact (hf.continuous_iteratedDeriv n (by simp)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc (fun x hx => iteratedDeriv_zero_off_interval hs n hx))

/-- Quantitative Fourier decay from an actual bounded derivative on fixed
compact support, proved using Fourier integration by parts. -/
theorem compact_fourier_power_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {l u C : ℝ} (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → f x = 0)
    (n : ℕ) (_hC : 0 ≤ C) (hb : ∀ x, ‖iteratedDeriv n f x‖ ≤ C) (ξ : ℝ) :
    |ξ|^n*‖𝓕 f ξ‖ ≤ (u-l)*C := by
  have hi : ∀ k : ℕ, k ≤ (⊤:ℕ∞) → Integrable (iteratedDeriv k f) :=
    fun k _ => compact_iteratedDeriv_integrable hf hs k
  have hF := congrFun (Real.fourier_iteratedDeriv (N := ⊤) hf hi (show (n:ℕ∞) ≤ ⊤ by simp)) ξ
  have hn : ‖𝓕 (iteratedDeriv n f) ξ‖ = (2*Real.pi)^n*|ξ|^n*‖𝓕 f ξ‖ := by
    rw [hF,norm_smul,norm_pow]
    simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    rw [show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
    ring
  have hp : 1 ≤ (2*Real.pi)^n := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hnorm : ‖𝓕 (iteratedDeriv n f) ξ‖ ≤ ∫ x, ‖iteratedDeriv n f x‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have hs' : ∀ x, x ∉ Icc l u → ‖iteratedDeriv n f x‖ = 0 := by
    intro x hx
    rw [iteratedDeriv_zero_off_interval hs n hx,norm_zero]
  have hiBound := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun x => ‖iteratedDeriv n f x‖) (s := Icc l u)
    isCompact_Icc.measure_lt_top (fun x _ => by simpa only [norm_norm] using hb x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs',Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),Real.volume_real_Icc_of_le hlu] at hiBound
  calc
    _ ≤ (2*Real.pi)^n*|ξ|^n*‖𝓕 f ξ‖ := by nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg (pow_nonneg (abs_nonneg ξ) n) (norm_nonneg (𝓕 f ξ)))]
    _ = ‖𝓕 (iteratedDeriv n f) ξ‖ := hn.symm
    _ ≤ C*(u-l) := hnorm.trans hiBound
    _ = _ := by ring

/-- Uniform rapid radial Fourier decay, with the constant chosen before
both ratio variables and the Fourier frequency. -/
theorem radial_uniform_power_decay {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v ∈ Icc v₀ v₁, ∀ y ∈ Icc y₀ y₁, ∀ ξ : ℝ,
      |ξ|^n*‖𝓕 (radialAmplitude a v y) ξ‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := radialAmplitude_uniform_deriv ha hs v₀ v₁ y₀ y₁ n
  refine ⟨(u-l)*C+1,by positivity,?_⟩
  intro v hv y hy ξ
  have hsup : ∀ r, r ∉ Icc l u → radialAmplitude a v y r = 0 := by
    intro r hr
    simp [radialAmplitude,hs r hr]
  exact (compact_fourier_power_bound (radialAmplitude_smooth ha v y) hlu hsup n hC.le (hb v hv y hy) ξ).trans (by linarith)

/-- Full one-plus-frequency decay, uniform on the fixed ratio box. -/
theorem radial_uniform_decay {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hlu : l ≤ u) (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v ∈ Icc v₀ v₁, ∀ y ∈ Icc y₀ y₁, ∀ ξ : ℝ,
      ‖𝓕 (radialAmplitude a v y) ξ‖ ≤ C/(1+|ξ|)^n := by
  obtain ⟨D₀,hD₀,h₀⟩ := radial_uniform_power_decay ha hlu hs v₀ v₁ y₀ y₁ 0
  obtain ⟨Dₙ,hDₙ,hₙ⟩ := radial_uniform_power_decay ha hlu hs v₀ v₁ y₀ y₁ n
  refine ⟨2^n*(D₀+Dₙ),by positivity,?_⟩
  intro v hv y hy ξ
  have hz : ‖𝓕 (radialAmplitude a v y) ξ‖ ≤ D₀ := by simpa using h₀ v hv y hy ξ
  have hn := hₙ v hv y hy ξ
  apply (le_div_iff₀ (pow_pos (by positivity) n)).mpr
  by_cases hx : |ξ| ≤ 1
  · calc
      _ ≤ D₀*2^n := mul_le_mul hz (pow_le_pow_left₀ (by positivity) (by linarith) n) (by positivity) hD₀.le
      _ ≤ _ := by nlinarith [show 0 ≤ (2:ℝ)^n*Dₙ by positivity]
  · have hx' : 1 ≤ |ξ| := (lt_of_not_ge hx).le
    calc
      _ ≤ ‖𝓕 (radialAmplitude a v y) ξ‖*(2*|ξ|)^n := by gcongr; linarith
      _ = 2^n*(|ξ|^n*‖𝓕 (radialAmplitude a v y) ξ‖) := by rw [mul_pow]; ring
      _ ≤ 2^n*Dₙ := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := by nlinarith [show 0 ≤ (2:ℝ)^n*D₀ by positivity]

/-- The actual radial integral equals the Fourier transform at L times the
strip's linear form, including the Jacobian factor r^2. -/
theorem radial_integral_fourier (a : ℝ → ℂ) (v y L m₁ m₂ m₃ : ℝ) :
    (∫ r, radialAmplitude a v y r * phase (-L*(m₁*v+m₂*y+m₃)*r)) =
      𝓕 (radialAmplitude a v y) (L*(m₁*v+m₂*y+m₃)) := by
  rw [fourier_eq_phase_integral]
  apply integral_congr_ae
  filter_upwards with r
  rw [show -L*(m₁*v+m₂*y+m₃)*r = -(L*(m₁*v+m₂*y+m₃))*r by ring]
  ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.compact_iteratedDeriv_integrable
#print axioms GuthMaynard.Improvement.compact_fourier_power_bound
#print axioms GuthMaynard.Improvement.radial_uniform_power_decay
#print axioms GuthMaynard.Improvement.radial_integral_fourier

#print axioms GuthMaynard.Improvement.radial_uniform_decay
