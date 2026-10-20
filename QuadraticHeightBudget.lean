module
public import QuadraticWindow

@[expose] public section

open Filter
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment

/-- The apparently resonant R² term in the quadratic estimate is actually
absorbed, with the normalized detector loss included. -/
theorem quadratic_diagonal_budget {σ a δ A : ℝ}
    (hw : QuadraticWindow σ a) (_hA : 0 < A)
    (_hδ : 0 ≤ δ) (hsmall : 9*δ < a*(4*σ-3)) :
    ∀ᶠ T : ℝ in atTop, 1 < T ∧ ∀ N : ℝ, 0 < N → T^a ≤ N →
      2*A*T^δ*N^3 ≤ (N^σ*T^(-2*δ))^4 := by
  let g := a*(4*σ-3)-9*δ
  have hg : 0 < g := by dsimp [g]; linarith only [hsmall]
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hg).eventually_ge_atTop (2*A)] with T hT hTA
  refine ⟨hT,?_⟩
  intro N hN hlo
  have hTp : 0 < T := by linarith
  have he : 0 ≤ 4*σ-3 := by linarith [hw.sigma_low]
  have hn : T^(a*(4*σ-3)) ≤ N^(4*σ-3) := by
    rw [Real.rpow_mul hTp.le]
    exact Real.rpow_le_rpow (by positivity) hlo he
  have hc : 2*A*T^δ ≤ N^(4*σ-3)*T^(-8*δ) := by
    calc
      _ ≤ T^g*T^δ := mul_le_mul_of_nonneg_right hTA (by positivity)
      _ = T^(a*(4*σ-3))*T^(-8*δ) := by
        rw [← Real.rpow_add hTp,← Real.rpow_add hTp]
        congr 1
        dsimp [g]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hn (by positivity)
  have hnid : N^(4*σ-3)*N^3=N^(4*σ) := by
    rw [← Real.rpow_natCast N 3,← Real.rpow_add hN]
    congr 1
    ring
  have hvid : (N^σ*T^(-2*δ))^4=N^(4*σ)*T^(-8*δ) := by
    rw [mul_pow,← Real.rpow_natCast (N^σ) 4,← Real.rpow_mul hN.le,
      ← Real.rpow_natCast (T^(-2*δ)) 4,← Real.rpow_mul hTp.le]
    congr 1 <;> congr 1 <;> ring
  calc
    _ ≤ (N^(4*σ-3)*T^(-8*δ))*N^3 := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (N^(4*σ-3)*N^3)*T^(-8*δ) := by ring
    _ = _ := by rw [hnid,hvid]

end Montgomery.RationalMoment
