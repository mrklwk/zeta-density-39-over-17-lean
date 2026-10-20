module
public import SignedFiniteLargeValues

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement

/-- The intended amplified sixth-moment comparison for the actual finite
polynomial and actual centered matrices. Every amplifier and operator input
is proved. The signed cubic plus signed mixed trace is retained as a whole. -/
theorem finite_signed_amplified_moment (w : MathCollab.Density.ComparisonCutoff)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T N L : ℝ, 1 < T → 1 ≤ N → N ≤ L → L ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (V : ℝ), 0 ≤ V →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (W.card:ℝ)^3*V^6 ≤ C*T^η*((N*L)^3+(N^4/L)*
        ((Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^3)).re+
          (Matrix.trace (cutoffContinuousMatrix w.toReflectionCutoff L W*
            cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re)) := by
  have hδ : 0 < η/3 := by positivity
  obtain ⟨A,D,hA,hD,h⟩ := finite_signed_large_value_comparison w hδ
  let C₀ := (2*A*2^(η/3))^3
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨4*C₀*(D^3+2),by positivity,?_⟩
  intro T N L hT hN hNL hLT a ha W V hV hlarge hsep
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by linarith
  have hLp : 0 < L := hNp.trans_le hNL
  let P := A*(1+L)^(η/3)*(N+1)
  let Z := (Matrix.trace (cutoffCenteredMatrix w.toReflectionCutoff L W^3)).re+
    (Matrix.trace (cutoffContinuousMatrix w.toReflectionCutoff L W*
      cutoffCenteredMatrix w.toReflectionCutoff L W^2)).re
  have hP : 0 < P := by dsimp [P]; positivity
  have hgate := h N L hNp hNL a ha W V hV hlarge hsep
  change (L/(2*N))*(max (((W.card:ℝ)*V^2)/P-D*L) 0)^3 ≤ Z at hgate
  have hZ : 0 ≤ Z := le_trans (by positivity) hgate
  have hmass := spectral_mass_scalar (show 0 ≤ (W.card:ℝ)*V^2 by positivity) hP
    (show 0 ≤ D*L by positivity) (show 0 < L/(2*N) by positivity) hgate
  have hpcube : P^3 ≤ C₀*T^η*N^3 := by
    have hb : (1+L)^(η/3) ≤ 2^(η/3)*T^(η/3) := by
      calc
        _ ≤ (2*T)^(η/3) := Real.rpow_le_rpow (by positivity) (by linarith) hδ.le
        _ = _ := Real.mul_rpow (by norm_num) hTp.le
    have hp : P ≤ (2*A*2^(η/3))*T^(η/3)*N := by
      calc
        _ ≤ A*(2^(η/3)*T^(η/3))*(2*N) := by
          dsimp [P]
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hb hA.le
          · linarith
          · positivity
          · positivity
        _ = _ := by ring
    have he : (T^(η/3))^3 = T^η := by
      rw [← Real.rpow_natCast (T^(η/3)) 3,← Real.rpow_mul hTp.le]
      congr 1
      ring
    have hh := pow_le_pow_left₀ hP.le hp 3
    simpa only [mul_pow,he,C₀] using hh
  have heZ : Z/(L/(2*N)) = 2*(N/L)*Z := by field_simp
  rw [heZ] at hmass
  have hbr : (D*L)^3+2*(N/L)*Z ≤ (D^3+2)*(L^3+(N/L)*Z) := by
    have hp : 0 ≤ (D^3)*((N/L)*Z) := by positivity
    have hq : 0 ≤ 2*L^3 := by positivity
    nlinarith
  have hfinal : ((W.card:ℝ)*V^2)^3 ≤
      4*(C₀*T^η*N^3)*((D^3+2)*(L^3+(N/L)*Z)) := by
    exact hmass.trans (mul_le_mul (by nlinarith [hpcube]) hbr (by positivity) (by positivity))
  have he : N^3*(L^3+(N/L)*Z) = (N*L)^3+(N^4/L)*Z := by ring
  calc
    _ = ((W.card:ℝ)*V^2)^3 := by ring
    _ ≤ _ := hfinal
    _ = (4*C₀*(D^3+2))*T^η*((N*L)^3+(N^4/L)*Z) := by rw [← he]; ring

end Montgomery.RationalMoment
