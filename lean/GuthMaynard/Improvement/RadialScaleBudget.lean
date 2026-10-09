import GuthMaynard.Improvement.CubicModeCount
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

/-- Order fixed after eta and before all scales and densities. -/
theorem choose_radial_discard_order {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, ∀ T : ℝ, 1 ≤ T →
      T^(6+3*η)/(T^η)^n ≤ T^(-100:ℝ) := by
  let n := ⌈(106+3*η)/η⌉₊
  have hn : 106+3*η ≤ (n:ℝ)*η := (div_le_iff₀ hη).mp (Nat.le_ceil _)
  refine ⟨n,?_⟩
  intro T hT
  have hTp : 0 < T := by linarith
  rw [← Real.rpow_natCast (T^η) n, ← Real.rpow_mul hTp.le, ← Real.rpow_sub hTp]
  exact Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)

/-- Actual discarded radial sum. The time support may translate arbitrarily;
its length is at most T. All three Fourier factors and the complete L cubed
normalization occur in radialDiscard and in the left hand side. -/
theorem radial_discard_negligible {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hlu : l ≤ u)
    (hs : ∀ r, r ∉ Icc l u → a r = 0)
    (v₀ v₁ y₀ y₁ : ℝ) (hv : v₀ ≤ v₁) (hy : y₀ ≤ y₁)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T L t₀ t₁ : ℝ) (S : Finset (ℤ × (ℤ × ℤ))) (μ : ℝ → ℝ),
      1 ≤ T → 0 < L → L ≤ T^(1+η) → t₀ ≤ t₁ → t₁-t₀ ≤ T →
      S ⊆ cubicModes (T^(1+η)/L) → Measurable μ → (∀ t, 0 ≤ μ t) →
      Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) →
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in Icc v₀ v₁ ×ˢ Icc y₀ y₁,
          radialDiscard a μ L (T^η) m p)‖ ≤
        C*T^(-100:ℝ)*((v₁-v₀)*(y₁-y₀))*Real.sqrt (∫ t, μ t^2)^3 := by
  obtain ⟨n,hn⟩ := choose_radial_discard_order hη
  obtain ⟨C,hC,h⟩ := radial_truncated_discard_L2 ha hlu hs v₀ v₁ y₀ y₁ hv hy n
  refine ⟨C,hC,?_⟩
  intro T L t₀ t₁ S μ hT hL hLT ht hlen hS hm h0 hi h2 hsup
  have hTp : 0 < T := by linarith
  have hH : 0 < T^η := Real.rpow_pos_of_pos hTp _
  have hU : 1 ≤ T^(1+η)/L := (le_div_iff₀ hL).mpr (by simpa using hLT)
  have hsqrt : Real.sqrt (t₁-t₀) ≤ T := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact hTp.le
    · nlinarith
  have he : |L|^3*(T^(1+η)/L)^3*T^3 = T^(6+3*η) := by
    rw [abs_of_pos hL,div_pow]
    have hh : L^3*((T^(1+η))^(3:ℕ)/L^3)*T^3 = (T^(1+η))^(3:ℕ)*T^3 := by field_simp
    rw [hh,← Real.rpow_natCast (T^(1+η)) 3,← Real.rpow_mul hTp.le,
      ← Real.rpow_natCast T 3,← Real.rpow_add hTp]
    congr 1
    norm_num
    ring
  calc
    _ ≤ C*|L|^3*(T^(1+η)/L)^3/(T^η)^n*((v₁-v₀)*(y₁-y₀))*
        Real.sqrt (t₁-t₀)^3*Real.sqrt (∫ t, μ t^2)^3 :=
      h L (T^η) (T^(1+η)/L) t₀ t₁ S μ hH hU ht hS hm h0 hi h2 hsup
    _ ≤ C*|L|^3*(T^(1+η)/L)^3/(T^η)^n*((v₁-v₀)*(y₁-y₀))*
        T^3*Real.sqrt (∫ t, μ t^2)^3 := by gcongr
    _ = C*(T^(6+3*η)/(T^η)^n)*((v₁-v₀)*(y₁-y₀))*Real.sqrt (∫ t, μ t^2)^3 := by
      rw [← he]
      ring
    _ ≤ _ := by gcongr; exact hn T hT

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.choose_radial_discard_order
#print axioms GuthMaynard.Improvement.radial_discard_negligible
