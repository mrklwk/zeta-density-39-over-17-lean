module
public import Mathlib

@[expose] public section

noncomputable section
open scoped BigOperators
set_option autoImplicit false
namespace GuthMaynardStatement

/-- Full proved coefficient curve; the stronger branch is strictly above 3/4. -/
def densityCoefficient (σ : ℝ) : ℝ :=
  if σ ≤ 9/13 then 3/(2-σ)
  else if σ ≤ 5/7 then 18/(7*σ+3)
  else if σ ≤ 3/4 then 9/4
  else 3/(2*σ)

/-- All actual zeros inside the open critical strip and the inclusive cutoffs,
counted with their analytic multiplicities. Existence of the finite set is part
of this assertion, so the statement cannot become vacuous by lacking such a set. -/
def actualZeroBound (σ T B : ℝ) : Prop :=
  ∃ Z : Finset ℂ,
    (∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T) ∧
    ((∑ ρ ∈ Z, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤ B

/-- Bounded-coefficient polynomial on the dyadic interval (N,2N]. -/
def dirichletPolynomial (N : ℝ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊,
    a n * Complex.exp (((t*Real.log ((n:ℝ)/N) : ℝ) : ℂ)*Complex.I)

/-! Independent specification only. Intentional theorem holes are confined to
this Challenge; Solution never imports it. They are not proof premises. -/

/-- For each fixed sigma and positive epsilon, one constant works for all T>=2. -/
theorem full_curve (σ ε : ℝ) (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      actualZeroBound σ T (C*T^(densityCoefficient σ*(1-σ)+ε)) := by
  sorry

/-- One constant precedes both sigma and height throughout the entire strip. -/
theorem global_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      actualZeroBound σ T (C*T^((39/17)*(1-σ)+ε)) := by
  sorry

/-- The exact curve has a uniform constant on the left interval and on the
right with any fixed positive gap from 3/4. No whole-strip sharp uniformity is stated. -/
theorem uniform_away_boundary (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 →
      (σ ≤ 3/4 ∨ 3/4+δ ≤ σ) → 2 ≤ T →
      actualZeroBound σ T (C*T^(densityCoefficient σ*(1-σ)+ε)) := by
  sorry

/-- One constant precedes every scale, threshold, coefficient family and
separated observation set. The length and height range is explicit. -/
theorem middle_large_values :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N T V t₀ : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ N → N^(6/5:ℝ) ≤ T → T ≤ N^(5/3:ℝ) → 0 < V →
      (∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, V ≤ ‖dirichletPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*N^ε*(N^2/V^2+N^(18/7:ℝ)*T^(6/7:ℝ)/V^4) := by
  sorry

end GuthMaynardStatement
