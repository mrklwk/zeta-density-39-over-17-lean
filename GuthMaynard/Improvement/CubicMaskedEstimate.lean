module
public import GuthMaynard.Improvement.CubicFourierMoments
public import GuthMaynard.Improvement.CubicFourierStrip
public import GuthMaynard.Improvement.CubicMaskedSpatialBound

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement

/-- Complete actual masked near-region estimate, with ordinary Fourier
moments and all dyadic/affine/smoothing losses discharged. Constants precede
all masks, densities, scales and retained subsets. -/
theorem cubic_masked_near_estimate (a b : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η C T₀ : ℝ, 0 < η ∧ η < (4:ℝ)/5 ∧ 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (T L : ℝ) (μ : ℝ → ℝ) (A B Cmask D : Set ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      T₀ ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T → Measurable μ →
      (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      MeasurableSet A → MeasurableSet B → MeasurableSet Cmask → MeasurableSet D →
      (∀ ξ, -ξ ∈ A ↔ ξ ∈ A) → (∀ ξ, -ξ ∈ D ↔ ξ ∈ D) → B ⊆ D → Cmask ⊆ D →
      (∀ m ∈ S, m.1 ∈ poissonModes (T^(1+η)/L) ∧
        m.2.1 ∈ poissonModes (T^(1+η)/L) ∧ m.2.2 ∈ poissonModes (T^(1+η)/L)) →
      L^3*(∑ m ∈ S, ∫ p in Icc a b ×ˢ Icc a b, maskedRadialNearMass μ A B Cmask L (T^η) m p) ≤
        C*T^ε*Real.sqrt (∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)*
          (T^2*(∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)+
            T*L*Real.sqrt (∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4)) := by
  have hab : a ≤ b := ha1.trans hb1
  have hb : 0 < b := by linarith
  have hc : 0 < a/b := div_pos ha hb
  have hcd : a/b ≤ b/a :=
    ((div_le_one hb).mpr hab).trans ((one_le_div ha).mpr hab)
  obtain ⟨η,C,T₀,hη,hη1,hC,hT₀,h⟩ := cubic_fourier_moments a b (a/b) (b/a) ha hab hc hcd hε
  refine ⟨η,C,T₀,hη,hη1,hC,hT₀,?_⟩
  intro T L μ A B Cmask D S hT hLl hLu hm h0 h1 h2 hA hB hCmask hD hAsym hDsym hBD hCD hS
  have hTp : 0 < T := lt_of_lt_of_le (by linarith) hT
  have hLp : 0 < L := (Real.rpow_pos_of_pos hTp _).trans_le hLl
  have hn := (fourier_near_strip_sum hm h0 h1 h2 ha ha1 hb1 hA hB hCmask hD hAsym hDsym hBD hCD L (T^η) S).2
  exact (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ L^3)).trans
    (h T L μ A D S hT hLl hLu h0 h1 h2 hA hD hS).2

/-- Actual independently masked spatial cubic sum: complete near-region
estimate plus homogeneous negligible error. No radial, affine, moment or
trace estimate appears as a premise. The designated first mask is exact. -/
theorem cubic_masked_spatial_estimate {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η C T₀ : ℝ, 0 < η ∧ η < (4:ℝ)/5 ∧ 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (T L t₀ t₁ : ℝ) (μ : ℝ → ℝ) (A B Cmask D : Set ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      T₀ ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T → t₀ ≤ t₁ → t₁-t₀ ≤ T →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) →
      MeasurableSet A → MeasurableSet B → MeasurableSet Cmask → MeasurableSet D →
      (∀ ξ, -ξ ∈ A ↔ ξ ∈ A) → (∀ ξ, -ξ ∈ D ↔ ξ ∈ D) → B ⊆ D → Cmask ⊆ D →
      (∀ m ∈ S, m.1 ∈ poissonModes (T^(1+η)/L) ∧
        m.2.1 ∈ poissonModes (T^(1+η)/L) ∧ m.2.2 ∈ poissonModes (T^(1+η)/L)) →
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ x : Triple, maskedSpatialCubicMode a μ L m A B Cmask x)‖ ≤
        C*(T^ε*Real.sqrt (∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)*
          (T^2*(∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)+
            T*L*Real.sqrt (∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4)) +
          T^(-100:ℝ)*Real.sqrt (∫ t, μ t^2)^3) := by
  have hu : 0 < u := hl.trans_le hlu
  have hv : 0 < l/u := div_pos hl hu
  have hv1 : l/u ≤ 1 := (div_le_one hu).mpr hlu
  have hy1 : 1 ≤ u/l := (one_le_div hl).mpr hlu
  obtain ⟨η,Cm,T₀,hη,hη1,hCm,hT₀,hmoment⟩ := cubic_masked_near_estimate (l/u) (u/l) hv hv1 hy1 hε
  obtain ⟨Cn,Ct,hCn,hCt,hspatial⟩ := masked_spatial_near_tail_bound ha hl hlu hs hη
  let C := Cn*Cm+Ct*(u/l-l/u)^2
  have hC : 0 < C := add_pos_of_pos_of_nonneg (mul_pos hCn hCm) (by positivity)
  refine ⟨η,C,T₀,hη,hη1,hC,hT₀,?_⟩
  intro T L t₀ t₁ μ A B Cmask D S hT hLl hLu ht hlen hm h0 hi h2 hsup hA hB hCmask hD hAsym hDsym hBD hCD hS
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := (Real.rpow_pos_of_pos hTp _).trans_le hLl
  have hLT : L ≤ T^(1+η) := hLu.trans (by
    calc
      T = T^(1:ℝ) := (Real.rpow_one T).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
  have hSc : S ⊆ cubicModes (T^(1+η)/L) := by
    intro m hmS
    obtain ⟨h₁,h₂,h₃⟩ := hS m hmS
    exact (mem_cubicModes _ m).mpr ⟨((mem_poissonModes _ _).mp h₁).2,
      ((mem_poissonModes _ _).mp h₂).2,((mem_poissonModes _ _).mp h₃).2⟩
  have hn := hmoment T L μ A B Cmask D S hT hLl hLu hm h0 hi h2 hA hB hCmask hD hAsym hDsym hBD hCD hS
  have hb := (hspatial T L t₀ t₁ S μ A B Cmask hT1 hLp hLT ht hlen hSc hA hB hCmask hm h0 hi h2 hsup).2.2
  let X := T^ε*Real.sqrt (∫ ξ in A, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)*
    (T^2*(∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2)+T*L*Real.sqrt (∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4))
  let Y := T^(-100:ℝ)*Real.sqrt (∫ t, μ t^2)^3
  have hD2 : 0 ≤ ∫ ξ in D, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hCmC : Cn*Cm ≤ C := by dsimp [C]; nlinarith [mul_nonneg hCt.le (sq_nonneg (u/l-l/u)),mul_pos hCn hCm]
  have hCtC : Ct*(u/l-l/u)^2 ≤ C := by dsimp [C]; nlinarith [mul_nonneg hCt.le (sq_nonneg (u/l-l/u)),mul_pos hCn hCm]
  calc
    _ ≤ Cn*(L^3*(∑ m ∈ S, ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        maskedRadialNearMass μ A B Cmask L (T^η) m p)) + Ct*(u/l-l/u)^2*Y := by
      convert hb using 1
      dsimp [Y]
      ring
    _ ≤ Cn*(Cm*X)+Ct*(u/l-l/u)^2*Y := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ hCn.le
      simpa only [X,mul_assoc] using hn
    _ ≤ C*X+C*Y := by
      rw [← mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_right hCmC hX) (mul_le_mul_of_nonneg_right hCtC hY)
    _ = _ := by dsimp [X,Y]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.cubic_masked_near_estimate

#print axioms GuthMaynard.Improvement.cubic_masked_spatial_estimate
