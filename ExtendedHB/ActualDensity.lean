module
public import ExtendedHB.RightParameters
public import TraceAlternatives.CurrentDensityCurve

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Montgomery.ExtendedHB
open MathCollab.Density Montgomery.RationalMoment.RightDetector.Physical TaoTrudgianYang2025

/-- Exact extended Heath--Brown exponent on the full closed interval
supported by the proved universal trace and physical peak-tail inputs. -/
theorem density {σ ε : ℝ} (hlo : 7/8 ≤ σ) (hhi : σ ≤ 17/19) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*(1-σ)/(10*σ-7)+ε) := by
  have h := density_of_pair_universal_window exponentPair_BHB6 (by norm_num)
    (physicalWindow hlo hhi) (universalWindow hlo hhi)
    (longTailFirst hlo hhi) (longTailSecond hlo hhi) hε
  have he : 3*lengthExponent σ*(1-σ)=3*(1-σ)/(10*σ-7) := by
    unfold lengthExponent
    ring
  simpa only [he] using h

/-- Actual-zero continuation to every fixed sigma below one. This is a
proved consequence of existing analytic inputs, distinct from full HB. -/
theorem density_right {σ ε : ℝ} (hlo : 17/19 ≤ σ) (hhi : σ < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(6*(1-σ)/(σ+3)+ε) := by
  have h := density_of_pair_universal_window exponentPair_BHB6 (by norm_num)
    (rightPhysicalWindow hlo hhi) (rightUniversalWindow hlo hhi)
    (rightLongTailFirst hlo) (rightLongTailSecond hlo) hε
  have he : 3*rightLengthExponent σ*(1-σ)=6*(1-σ)/(σ+3) := by
    unfold rightLengthExponent
    ring
  simpa only [he] using h

theorem density_right_closed {σ ε : ℝ} (hlo : 17/19 ≤ σ) (_hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(6*(1-σ)/(σ+3)+ε) := by
  by_cases hlt : σ < 1
  · exact density_right hlo hlt hε
  · refine ⟨1,by norm_num,?_⟩
    intro T hT
    rw [zetaDensityCount_eq_zero_of_one_le (le_of_not_gt hlt)]
    simpa only [Nat.cast_zero,one_mul] using
      (Real.rpow_nonneg (by linarith : 0 ≤ T) (6*(1-σ)/(σ+3)+ε))

theorem literal_density (σ ε : ℝ) (hlo : 7/8 ≤ σ) (hhi : σ ≤ 17/19) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ∈F ↔ riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧ σ≤ρ.re ∧ |ρ.im|≤T) →
      ((∑ ρ∈F, analyticOrderNatAt riemannZeta ρ : ℕ):ℝ) ≤ C*T^(3*(1-σ)/(10*σ-7)+ε) := by
  obtain ⟨C,hC,h⟩ := density hlo hhi hε
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F=zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero,and_assoc]
  simpa only [he,zetaDensityCount,zetaSlabCount,zetaMultiplicity] using h T hT

theorem literal_density_right (σ ε : ℝ) (hlo : 17/19 ≤ σ) (hhi : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ∈F ↔ riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧ σ≤ρ.re ∧ |ρ.im|≤T) →
      ((∑ ρ∈F, analyticOrderNatAt riemannZeta ρ : ℕ):ℝ) ≤ C*T^(6*(1-σ)/(σ+3)+ε) := by
  obtain ⟨C,hC,h⟩ := density_right_closed hlo hhi hε
  refine ⟨C,hC,?_⟩
  intro T hT F hF
  have he : F=zetaZeroFinset σ (-T) T := by
    ext ρ
    rw [hF,mem_zetaDensityFinset]
    simp only [IsNontrivialZetaZero,and_assoc]
  simpa only [he,zetaDensityCount,zetaSlabCount,zetaMultiplicity] using h T hT

end Montgomery.ExtendedHB
