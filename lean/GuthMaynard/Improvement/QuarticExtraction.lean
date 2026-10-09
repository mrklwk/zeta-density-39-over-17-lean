import GuthMaynard.Improvement.QuarticMomentExtraction
import GuthMaynard.Improvement.QuarticBadCells
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Separated-value extraction from the literal truncated fourth moment.
All kernel, packing, bad-cell and rapid-tail estimates are discharged. The
remaining analytic hypothesis is exactly the displayed actual moment bound;
the radius condition is purely scalar and uniform in the polynomial. -/
theorem quartic_extraction {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T R U V M : ℝ,
      2 ≤ N → N ≤ T → T ≤ N^2 → 0 < R → R ≤ T → 0 < U → 0 < V →
      C*N^4/R^q ≤ V^4/2 →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      MathCollab.Density.oneSeparated W → (∀ w ∈ W, w ∈ Icc (0:ℝ) T) →
      (∀ w ∈ W, V ≤ ‖boundedPolynomial N a w‖) →
      (∫ t, (sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T))
        (boundedPolynomial N a) U t)^2) ≤ M →
      (W.card:ℝ) ≤ C*((R+1)*N^ε*(N^2/U^2+T*N^4/U^6)+M/V^4) := by
  obtain ⟨B,hB,hb⟩ := quartic_moment_extraction q
  obtain ⟨D,hD,hd⟩ := quartic_bad_cells_bound hε
  let C := B+3*D+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hDC : 3*D ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro N T R U V M hN hNT hTN hR hRT hU hV hsmall a W ha hsep hw hv hM
  have hT : 0 < T := by linarith
  have hm : 0 ≤ M := (integral_nonneg (fun t => sq_nonneg
    (sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U t))).trans hM
  have hsmallB : B*N^4/R^q ≤ V^4/2 := by
    apply le_trans _ hsmall
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC (by positivity)) (by positivity)
  have he := hb N T R U V M hN hT hR hRT hV hsmallB a W ha hsep hw hv hM
  have hk := hd N T U hN hNT hTN hU a ha
  have hx : 0 ≤ N^ε*(N^2/U^2+T*N^4/U^6) := by positivity
  calc
    _ ≤ (2*R+3)*(D*N^ε*(N^2/U^2+T*N^4/U^6))+B*M/V^4 :=
      he.trans (add_le_add (mul_le_mul_of_nonneg_left hk (show 0 ≤ 2*R+3 by positivity)) le_rfl)
    _ ≤ C*((R+1)*N^ε*(N^2/U^2+T*N^4/U^6))+C*(M/V^4) := by
      apply add_le_add
      · have hcoeff : (2*R+3)*D ≤ C*(R+1) := by
          have hh := mul_le_mul_of_nonneg_right hDC (show 0 ≤ R+1 by positivity)
          nlinarith
        convert mul_le_mul_of_nonneg_right hcoeff hx using 1 <;> ring
      · rw [div_eq_mul_inv,div_eq_mul_inv]
        convert mul_le_mul_of_nonneg_right hBC (show 0 ≤ M*(V^4)⁻¹ by positivity) using 1; ring
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.quartic_extraction
