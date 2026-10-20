module
public import TraceAlternatives.UniversalQuadraticLevelCount
public import TraceAlternatives.NativeNormalizedPhase

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

/-- Literal negative-phase natural-scale form of the actual universal
quadratic level-count producer. All normalization changes are unitary. -/
theorem universal_native_quadratic_level_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (N : ℕ) (T V : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < N → 2 ≤ T → (N:ℝ) ≤ T → 0 < V →
        D*T^ε*(N:ℝ)^3 ≤ V^4 →
        (∀ n ∈ Ioc N (2*N), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card:ℝ) ≤ C*T^ε*((N:ℝ)^2*V^(-2:ℝ)+
          (N:ℝ)^(8/3:ℝ)*T^(2/3:ℝ)*V^(-4:ℝ)+
          (N:ℝ)^(36/5:ℝ)*T^(3/5:ℝ)*V^(-48/5:ℝ)) := by
  obtain ⟨C,D,hC,hD,hCount⟩ := universal_quadratic_level_count ε hε
  refine ⟨C,D,hC,hD,?_⟩
  intro N T V a W hN hT hNT hV hCut ha hSep hBase hLarge
  apply hCount T 0 N V hT (by exact_mod_cast hN) hNT hV hCut
    (conjugateCoeffs a) ?_ W ?_ hSep ?_
  · intro n hn
    change n ∈ sourceRatioIndices (N:ℝ) at hn
    rw [sourceRatioIndices_nat] at hn
    rw [norm_conjugateCoeffs]
    exact ha n hn
  · intro t ht
    simpa only [zero_add] using hBase t ht
  · intro t ht
    rw [norm_boundedPolynomial_native_conjugate hN]
    exact hLarge t ht

end Montgomery.RationalMoment
