module
public import QuadraticScalarMass

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The intended amplified fourth-moment comparison for the actual finite
polynomial and actual centered matrices. Every amplifier and operator input
is proved. The centered quadratic trace is retained. -/
theorem finite_quadratic_amplified_moment (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T N L : ℝ, 1 < T → 1 ≤ N → N ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^2*V^4 ≤ C*T^η*((N*L)^2+(N^3/L)*
        (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re) := by
  have hδ : 0 < η/2 := by positivity
  obtain ⟨A,D,hA,hD,h⟩ := finite_quadratic_large_value_comparison w hδ
  let C₀ := (2*A*2^(η/2))^2
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨4*C₀*(D^2+2),by positivity,?_⟩
  intro T N L hT hN hNL hLT a ha W V hV hlarge hsep
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by linarith
  have hLp : 0 < L := hNp.trans_le hNL
  let P := A*(1+L)^(η/2)*(N+1)
  let Z := (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re
  have hP : 0 < P := by dsimp [P]; positivity
  have hgate := h N L hNp hNL a ha W V hV hlarge hsep
  change (L/(2*N))*(max (((W.card:ℝ)*V^2)/P-D*L) 0)^2 ≤ Z at hgate
  have hZ : 0 ≤ Z := le_trans (by positivity) hgate
  have hmass := quadratic_mass_scalar (show 0 ≤ (W.card:ℝ)*V^2 by positivity) hP
    (show 0 ≤ D*L by positivity) (show 0 < L/(2*N) by positivity) hgate
  have hpcube : P^2 ≤ C₀*T^η*N^2 := by
    have hb : (1+L)^(η/2) ≤ 2^(η/2)*T^(η/2) := by
      calc
        _ ≤ (2*T)^(η/2) := Real.rpow_le_rpow (by positivity) (by linarith) hδ.le
        _ = _ := Real.mul_rpow (by norm_num) hTp.le
    have hp : P ≤ (2*A*2^(η/2))*T^(η/2)*N := by
      calc
        _ ≤ A*(2^(η/2)*T^(η/2))*(2*N) := by
          dsimp [P]
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hb hA.le
          · linarith
          · positivity
          · positivity
        _ = _ := by ring
    have he : (T^(η/2))^2 = T^η := by
      rw [← Real.rpow_natCast (T^(η/2)) 2,← Real.rpow_mul hTp.le]
      congr 1
      ring
    have hh := pow_le_pow_left₀ hP.le hp 2
    simpa only [mul_pow,he,C₀] using hh
  have heZ : Z/(L/(2*N)) = 2*(N/L)*Z := by field_simp
  rw [heZ] at hmass
  have hbr : (D*L)^2+2*(N/L)*Z ≤ (D^2+2)*(L^2+(N/L)*Z) := by
    have hp : 0 ≤ (D^2)*((N/L)*Z) := by positivity
    have hq : 0 ≤ 2*L^2 := by positivity
    nlinarith
  have hfinal : ((W.card:ℝ)*V^2)^2 ≤
      4*(C₀*T^η*N^2)*((D^2+2)*(L^2+(N/L)*Z)) := by
    exact hmass.trans (mul_le_mul (by nlinarith [hpcube]) hbr (by positivity) (by positivity))
  have he : N^2*(L^2+(N/L)*Z) = (N*L)^2+(N^3/L)*Z := by ring
  calc
    _ = ((W.card:ℝ)*V^2)^2 := by ring
    _ ≤ _ := hfinal
    _ = (4*C₀*(D^2+2))*T^η*((N*L)^2+(N^3/L)*Z) := by rw [← he]; ring

end Montgomery.RationalMoment
