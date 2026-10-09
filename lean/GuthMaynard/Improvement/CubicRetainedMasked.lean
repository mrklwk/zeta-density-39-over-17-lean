import GuthMaynard.Improvement.CubicMaskedEstimate
import GuthMaynard.Improvement.CubicRetainedPartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

/-- The actual retained kernel cubic with an arbitrary symmetric designated
Fourier mask. All constants precede the density and mask. -/
theorem retained_masked_cubic_estimate {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η C T₀ : ℝ, 0 < η ∧ η < (4:ℝ)/5 ∧ 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (T L t₀ t₁ : ℝ) (μ : ℝ → ℝ) (A : Set ℝ),
      T₀ ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T → t₀ ≤ t₁ → t₁-t₀ ≤ T →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) → MeasurableSet A →
      (∀ ξ, -ξ ∈ A ↔ ξ ∈ A) →
      let M := ∫ t, μ t^2
      let E := ∫ ξ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4
      let E₀ := ∫ ξ in Aᶜ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4
      let A₂ := ∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2
      ‖kernelCubic (timeMeasure μ)
        (retainedPoissonKernel (volume.restrict (Icc l u)) a L (poissonModes (T^(1+η)/L)))‖ ≤
        C*T^ε*(T^2*M*Real.sqrt M+T*L*Real.sqrt M*Real.sqrt E₀+
          Real.sqrt A₂*(T^2*M+T*L*Real.sqrt E)) := by
  obtain ⟨η,C,T₀,hη,hη1,hC,hT₀,h⟩ := cubic_masked_spatial_estimate ha hl hlu hs hε
  refine ⟨η,8*C,T₀,hη,hη1,by positivity,hT₀,?_⟩
  intro T L t₀ t₁ μ A hT hLl hLu ht hlen hm h0 hi h2 hsup hA hAsym
  let M := ∫ t, μ t^2
  let E := ∫ ξ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4
  let E₀ := ∫ ξ in Aᶜ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4
  let A₂ := ∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2
  let Q := ∫ ξ in Aᶜ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2
  let U := T^(1+η)/L
  let X := T^2*M*Real.sqrt M+T*L*Real.sqrt M*Real.sqrt E₀
  let Y := Real.sqrt A₂*(T^2*M+T*L*Real.sqrt E)
  let Z := T^(-100:ℝ)*Real.sqrt M^3
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := (Real.rpow_pos_of_pos hTp _).trans_le hLl
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  have hQ : 0 ≤ Q := integral_nonneg (fun _ => sq_nonneg _)
  have hQM : Q ≤ M := by
    calc
      _ ≤ ∫ ξ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2 :=
        setIntegral_le_integral (ordinary_real_fourier_square_integrable hi h2)
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      _ = _ := ordinary_real_fourier_integral_square hi h2
  have hAc : ∀ ξ, -ξ ∈ Aᶜ ↔ ξ ∈ Aᶜ := fun ξ => not_congr (hAsym ξ)
  have hUniv : ∀ ξ : ℝ, -ξ ∈ (univ : Set ℝ) ↔ ξ ∈ (univ : Set ℝ) := by simp
  have hS : ∀ m ∈ retainedCubicModes U, m.1 ∈ poissonModes U ∧
      m.2.1 ∈ poissonModes U ∧ m.2.2 ∈ poissonModes U :=
    fun m hm => (retainedCubicModes_mem U m).mp hm
  have hlow := h T L t₀ t₁ μ Aᶜ Aᶜ Aᶜ Aᶜ (retainedCubicModes U)
    hT hLl hLu ht hlen hm h0 hi h2 hsup hA.compl hA.compl hA.compl hA.compl
    hAc hAc Subset.rfl Subset.rfl hS
  have hhigh₁ := h T L t₀ t₁ μ A univ univ univ (retainedCubicModes U)
    hT hLl hLu ht hlen hm h0 hi h2 hsup hA MeasurableSet.univ MeasurableSet.univ MeasurableSet.univ
    hAsym hUniv Subset.rfl Subset.rfl hS
  have hhigh₂ := h T L t₀ t₁ μ A univ Aᶜ univ (retainedCubicModes U)
    hT hLl hLu ht hlen hm h0 hi h2 hsup hA MeasurableSet.univ hA.compl MeasurableSet.univ
    hAsym hUniv Subset.rfl (subset_univ _) hS
  have hhigh₃ := h T L t₀ t₁ μ A Aᶜ Aᶜ univ (retainedCubicModes U)
    hT hLl hLu ht hlen hm h0 hi h2 hsup hA hA.compl hA.compl MeasurableSet.univ
    hAsym hUniv (subset_univ _) (subset_univ _) hS
  have hlow' : ‖maskedRetainedCubic a μ L U Aᶜ Aᶜ Aᶜ‖ ≤ C*(T^ε*X+Z) := by
    apply hlow.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply add_le_add _ le_rfl
    calc
      _ ≤ T^ε*Real.sqrt M*(T^2*M+T*L*Real.sqrt E₀) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQM) (Real.rpow_nonneg hTp.le _)
        · exact add_le_add (mul_le_mul_of_nonneg_left hQM (sq_nonneg T)) le_rfl
        · positivity
        · positivity
      _ = T^ε*X := by dsimp [X]; ring
  have hh₁ : ‖maskedRetainedCubic a μ L U A univ univ‖ ≤ C*(T^ε*Y+Z) := by
    simpa only [maskedRetainedCubic, Y, Z, M, E, A₂, mul_assoc, setIntegral_univ,ordinary_real_fourier_integral_square hi h2] using hhigh₁
  have hh₂ : ‖maskedRetainedCubic a μ L U A univ Aᶜ‖ ≤ C*(T^ε*Y+Z) := by
    simpa only [maskedRetainedCubic, Y, Z, M, E, A₂, mul_assoc, setIntegral_univ,ordinary_real_fourier_integral_square hi h2] using hhigh₂
  have hh₃ : ‖maskedRetainedCubic a μ L U A Aᶜ Aᶜ‖ ≤ C*(T^ε*Y+Z) := by
    simpa only [maskedRetainedCubic, Y, Z, M, E, A₂, mul_assoc, setIntegral_univ,ordinary_real_fourier_integral_square hi h2] using hhigh₃
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hZ : Z ≤ T^ε*X := by
    have hpow : T^(-100:ℝ) ≤ T^ε*T^2 := by
      rw [← Real.rpow_natCast T 2,← Real.rpow_add hTp]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    have hsqrt : Real.sqrt M^3 = M*Real.sqrt M := by
      calc
        _ = (Real.sqrt M)^2*Real.sqrt M := by ring
        _ = _ := by rw [Real.sq_sqrt hM]
    calc
      Z = T^(-100:ℝ)*(M*Real.sqrt M) := by dsimp only [Z]; rw [hsqrt]
      _ ≤ (T^ε*T^2)*(M*Real.sqrt M) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ T^ε*X := by dsimp [X]; nlinarith [mul_nonneg (Real.rpow_nonneg hTp.le ε) (show 0 ≤ T*L*Real.sqrt M*Real.sqrt E₀ by positivity)]
  have hnorm : ‖kernelCubic (timeMeasure μ)
      (retainedPoissonKernel (volume.restrict (Icc l u)) a L (poissonModes U))‖ ≤
      C*(T^ε*X+Z)+C*(T^ε*Y+Z)+C*(T^ε*Y+Z)+C*(T^ε*Y+Z) := by
    rw [retained_cubic_designated_partition ha hl hlu hs hm h0 hi L U hA]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add hlow' hh₁)) hh₂)) hh₃)
  calc
    _ ≤ C*(T^ε*X+Z)+C*(T^ε*Y+Z)+C*(T^ε*Y+Z)+C*(T^ε*Y+Z) := hnorm
    _ ≤ (8*C)*T^ε*(X+Y) := by
      nlinarith [mul_le_mul_of_nonneg_left hZ hC.le,
        mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hTp.le ε)) hX,
        mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hTp.le ε)) hY]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.retained_masked_cubic_estimate
