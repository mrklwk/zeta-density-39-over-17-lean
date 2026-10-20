module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosSevenCount
public import LaterPairs.Native.RobertSargosTaylorSystem

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                
                                                                       

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargosTaylorQuadratic_eq (r q h n : ℝ) :
    robertSargosTaylorQuadratic r q h n =
      robertSargosQuadratic (-r) q h n-r*h^2-r^2*h := by
  unfold robertSargosTaylorQuadratic robertSargosQuadratic
  ring

theorem robertSargos_taylor_remainder_le {R H r h : ℝ}
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hRH : R ≤ H)
    (hr : |r| ≤ R) (hh : |h| ≤ 2*H) :
    |r*h^2+r^2*h| ≤ 6*R*H^2 := by
  have hr2 : r^2 ≤ R^2 := by
    have ht := sq_le_sq₀ (abs_nonneg r) hR |>.mpr hr
    simpa only [sq_abs] using ht
  have hh2 : h^2 ≤ (2*H)^2 := by
    have ht := sq_le_sq₀ (abs_nonneg h) (by positivity : 0 ≤ 2*H) |>.mpr hh
    simpa only [sq_abs] using ht
  have hR2 : R^2 ≤ R*H := by nlinarith [mul_nonneg hR (sub_nonneg.mpr hRH)]
  calc
    _ ≤ |r*h^2|+|r^2*h| := abs_add_le _ _
    _ = |r| * h^2+r^2*|h| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg h),abs_of_nonneg (sq_nonneg r)]
    _ ≤ R*(2*H)^2+R^2*(2*H) :=
      add_le_add (mul_le_mul hr hh2 (sq_nonneg h) hR)
        (mul_le_mul hr2 hh (abs_nonneg h) (sq_nonneg R))
    _ ≤ 6*R*H^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hR2 hH]

/-- The actual Taylor phase is reduced only after charging both omitted
terms to the tolerance, as required in the paper's Step 7. -/
theorem robertSargos_actual_to_counting_tolerance {R H r q₁ q₂ h₁ h₂ n₁ n₂ E : ℝ}
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hRH : R ≤ H)
    (hr : |r| ≤ R) (hh₁ : |h₁| ≤ 2*H) (hh₂ : |h₂| ≤ 2*H)
    (hlin : robertSargosLinear (-r) q₁ h₁ n₁ =
      robertSargosLinear (-r) q₂ h₂ n₂)
    (hnear : |robertSargosTaylorQuadratic r q₁ h₁ n₁-
      robertSargosTaylorQuadratic r q₂ h₂ n₂| ≤ E) :
    |robertSargosReduced (-r) q₁ q₂ h₁ h₂ (n₁-n₂)| ≤ E+12*R*H^2 := by
  rw [← robertSargos_quadratic_difference hlin]
  have hrem₁ := robertSargos_taylor_remainder_le hR hH hRH hr hh₁
  have hrem₂ := robertSargos_taylor_remainder_le hR hH hRH hr hh₂
  calc
    _ = |(robertSargosTaylorQuadratic r q₁ h₁ n₁-
        robertSargosTaylorQuadratic r q₂ h₂ n₂)+(r*h₁^2+r^2*h₁)-
        (r*h₂^2+r^2*h₂)| := by
      congr 1
      simp only [robertSargosTaylorQuadratic_eq]
      ring
    _ ≤ |robertSargosTaylorQuadratic r q₁ h₁ n₁-
        robertSargosTaylorQuadratic r q₂ h₂ n₂|+
        |r*h₁^2+r^2*h₁|+|r*h₂^2+r^2*h₂| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

theorem RobertSargosTaylorSystem.counting_near {R H Q N E : ℝ}
    {p : RobertSargosSevenPoint} (h : RobertSargosTaylorSystem R H Q N E p)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hRH : R ≤ H) :
    |robertSargosQuadratic (-p.r) p.q₁ p.h₁ p.n₁-
      robertSargosQuadratic (-p.r) p.q₂ p.h₂ p.n₂| ≤ E+12*R*H^2 := by
  have hline : robertSargosLinear (-(p.r:ℝ)) p.q₁ p.h₁ p.n₁ =
      robertSargosLinear (-(p.r:ℝ)) p.q₂ p.h₂ p.n₂ := by
    unfold robertSargosLinear
    have ht : (p.h₁:ℝ)*p.q₁-p.r*p.n₁ = p.h₂*p.q₂-p.r*p.n₂ := by
      exact_mod_cast h.linear
    linarith
  have hh₁ : |(p.h₁:ℝ)| ≤ 2*H := by
    rw [abs_of_nonneg (hH.trans h.h₁_support.1)]
    exact h.h₁_support.2
  have hh₂ : |(p.h₂:ℝ)| ≤ 2*H := by
    rw [abs_of_nonneg (hH.trans h.h₂_support.1)]
    exact h.h₂_support.2
  rw [robertSargos_quadratic_difference hline]
  exact robertSargos_actual_to_counting_tolerance hR hH hRH h.r_bound hh₁ hh₂
    hline h.near

theorem RobertSargosTaylorSystem.to_counting {R H Q N E δ : ℝ}
    {p : RobertSargosSevenPoint} (h : RobertSargosTaylorSystem R H Q N E p)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hRH : R ≤ H)
    (hδ : E+12*R*H^2 ≤ δ*H*Q^2) :
    RobertSargosSevenSystem R H Q N δ (robertSargosReverseR p) := by
  refine ⟨neg_ne_zero.mpr h.r_ne_zero,?_,h.q₁_support,h.q₂_support,
    h.h₁_support,h.h₂_support,h.n₁_support,h.n₂_support,h.same_sign,?_,?_⟩
  · simpa only [robertSargosReverseR,Int.cast_neg,abs_neg] using h.r_bound
  · change (-p.r)*p.n₁+p.h₁*p.q₁ = (-p.r)*p.n₂+p.h₂*p.q₂
    linarith only [h.linear]
  · simpa only [robertSargosReverseR,Int.cast_neg] using
      (h.counting_near hR hH hRH).trans hδ



theorem exists_robertSargos_taylor_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosSevenPoint) (R H Q N E : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 1 ≤ N → 0 ≤ E → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosTaylorSystem R H Q N E p) →
      (S.card:ℝ) ≤ C*(R*N*H*Q)^(1+ε)*(1+(E+12*R*H^2)/(H*Q)) := by
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_seven_count ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q N E hR hH hQ hN hE hRH hS
  have hHp : 0 < H := by linarith
  have hQp : 0 < Q := by linarith
  let δ := (E+12*R*H^2)/(H*Q^2)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hscale : E+12*R*H^2 = δ*H*Q^2 := by
    dsimp [δ]
    field_simp
  have hcard : (S.image robertSargosReverseR).card = S.card :=
    Finset.card_image_of_injective S robertSargos_reverseR_injective
  have ht := hcount (S.image robertSargosReverseR) R H Q N δ hR hH hQ hN hδ hRH
    (by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact (hS q hq).to_counting (by linarith) hHp.le (by linarith) hscale.le)
  have hfactor : 1+δ*Q = 1+(E+12*R*H^2)/(H*Q) := by
    dsimp [δ]
    field_simp
  rwa [hcard,hfactor] at ht

end TaoTrudgianYang2025
