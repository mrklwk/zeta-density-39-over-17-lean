module
public import FinalDensitySurface.Providers

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace FinalDensitySurface
open MathCollab.Density

/-- Exact literal density statement for plotted piece G1, including its graph endpoints. -/
theorem piece_G1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((-3/(σ - 2))*(1-σ)) + ε) := by
  exact provider_P1 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece G2, including its graph endpoints. -/
theorem piece_G2 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε) := by
  by_cases hend : σ = (19/25 : ℝ)
  · subst σ
    convert (provider_P3 (σ := (19/25 : ℝ)) (ε := ε) (by norm_num) (by norm_num) hε) using 1
    all_goals norm_num
  · exact provider_P2 (σ := σ) (ε := ε) (by linarith) (lt_of_le_of_ne hhi hend) hε

/-- Exact literal density statement for plotted piece G3, including its graph endpoints. -/
theorem piece_G3 {σ ε : ℝ} (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε) := by
  exact provider_P3 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece G4, including its graph endpoints. -/
theorem piece_G4 {σ ε : ℝ} (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε) := by
  exact provider_P4 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece G5, including its graph endpoints. -/
theorem piece_G5 {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε) := by
  by_cases hend : σ = (17/22 : ℝ)
  · subst σ
    convert (provider_P6 (σ := (17/22 : ℝ)) (ε := ε) (by norm_num) (by norm_num) hε) using 1
    all_goals norm_num
  · exact provider_P5 (σ := σ) (ε := ε) (by linarith) (lt_of_le_of_ne hhi hend) hε

/-- Exact literal density statement for plotted piece G6, including its graph endpoints. -/
theorem piece_G6 {σ ε : ℝ} (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε) := by
  exact provider_P6 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece G7, including its graph endpoints. -/
theorem piece_G7 {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε) := by
  by_cases hend : σ = (7/9 : ℝ)
  · subst σ
    convert (provider_P8 (σ := (7/9 : ℝ)) (ε := ε) (by norm_num) (by norm_num) hε) using 1
    all_goals norm_num
  · exact provider_P7 (σ := σ) (ε := ε) (by linarith) (lt_of_le_of_ne hhi hend) hε

/-- Exact literal density statement for plotted piece G8, including its graph endpoints. -/
theorem piece_G8 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (23/29 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε) := by
  exact provider_P8 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece G9, including its graph endpoints. -/
theorem piece_G9 {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(2*σ))*(1-σ)) + ε) := by
  exact provider_P9 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece G10, including its graph endpoints. -/
theorem piece_G10 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε) := by
  exact provider_P10 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece B1, including its graph endpoints. -/
theorem piece_B1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((-3/(σ - 2))*(1-σ)) + ε) := by
  exact provider_P1 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece B2, including its graph endpoints. -/
theorem piece_B2 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((18/(7*σ+3))*(1-σ)) + ε) := by
  exact provider_P11 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece B3, including its graph endpoints. -/
theorem piece_B3 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (11/15 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((9/4)*(1-σ)) + ε) := by
  exact provider_P12 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece B4, including its graph endpoints. -/
theorem piece_B4 {σ ε : ℝ} (hlo : (11/15 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε) := by
  exact provider_P2 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece B5, including its graph endpoints. -/
theorem piece_B5 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(2*σ))*(1-σ)) + ε) := by
  exact provider_P13 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece B6, including its graph endpoints. -/
theorem piece_B6 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε) := by
  exact provider_P10 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O1, including its graph endpoints. -/
theorem piece_O1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((-3/(σ - 2))*(1-σ)) + ε) := by
  exact provider_P1 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O2, including its graph endpoints. -/
theorem piece_O2 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (12/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((18/(7*σ+3))*(1-σ)) + ε) := by
  exact provider_P11 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O3, including its graph endpoints. -/
theorem piece_O3 {σ ε : ℝ} (hlo : (12/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(8*σ-3))*(1-σ)) + ε) := by
  exact provider_P14 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O4, including its graph endpoints. -/
theorem piece_O4 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((12/(9*σ-1))*(1-σ)) + ε) := by
  exact provider_P15 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O5, including its graph endpoints. -/
theorem piece_O5 {σ ε : ℝ} (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((255/(153*σ+7))*(1-σ)) + ε) := by
  exact provider_P16 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O6, including its graph endpoints. -/
theorem piece_O6 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(2*σ))*(1-σ)) + ε) := by
  exact provider_P13 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O7, including its graph endpoints. -/
theorem piece_O7 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(11*σ-7))*(1-σ)) + ε) := by
  exact provider_P17 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O8, including its graph endpoints. -/
theorem piece_O8 {σ ε : ℝ} (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε) := by
  exact provider_P18 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O9, including its graph endpoints. -/
theorem piece_O9 {σ ε : ℝ} (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε) := by
  exact provider_P19 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O10, including its graph endpoints. -/
theorem piece_O10 {σ ε : ℝ} (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε) := by
  exact provider_P20 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O11, including its graph endpoints. -/
theorem piece_O11 {σ ε : ℝ} (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε) := by
  exact provider_P21 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O12, including its graph endpoints. -/
theorem piece_O12 {σ ε : ℝ} (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((566/(606*σ-173))*(1-σ)) + ε) := by
  exact provider_P22 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O13, including its graph endpoints. -/
theorem piece_O13 {σ ε : ℝ} (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε) := by
  exact provider_P23 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O14, including its graph endpoints. -/
theorem piece_O14 {σ ε : ℝ} (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε) := by
  exact provider_P24 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O15, including its graph endpoints. -/
theorem piece_O15 {σ ε : ℝ} (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε) := by
  exact provider_P25 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O16, including its graph endpoints. -/
theorem piece_O16 {σ ε : ℝ} (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε) := by
  exact provider_P26 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O17, including its graph endpoints. -/
theorem piece_O17 {σ ε : ℝ} (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε) := by
  exact provider_P27 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O18, including its graph endpoints. -/
theorem piece_O18 {σ ε : ℝ} (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε) := by
  exact provider_P28 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O19, including its graph endpoints. -/
theorem piece_O19 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (24139/27578 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ ((1086/5537) + ε) := by
  exact provider_P29 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O20, including its graph endpoints. -/
theorem piece_O20 {σ ε : ℝ} (hlo : (24139/27578 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((24/(30*σ-11))*(1-σ)) + ε) := by
  exact provider_P30 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O21, including its graph endpoints. -/
theorem piece_O21 {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/19 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(σ+3))*(1-σ)) + ε) := by
  exact provider_P31 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- Exact literal density statement for plotted piece O22, including its graph endpoints. -/
theorem piece_O22 {σ ε : ℝ} (hlo : (17/19 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε) := by
  exact provider_P10 (σ := σ) (ε := ε) (by linarith) (by linarith) hε

/-- One constant before all cutoffs on the full plateau range. -/
theorem uniform_P29 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/8 : ℝ) ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ ((1086/5537 : ℝ) + ε) := by
  obtain ⟨C,hC,h⟩ := Montgomery.MonotoneCurve.seven_eighths_right_uniform hε
  refine ⟨C,hC,?_⟩
  intro σ T hlo _hhi hT F hF
  rw [← exact_count_identity σ T F hF]
  exact h σ hlo T hT

/-- Verified recovered-family uniform quantifier order, separate from original analytic-route status. -/
theorem uniform_P30 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22 : ℝ) ≤ σ → σ ≤ (23/26 : ℝ) → 2 ≤ T →
      ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((24/(30*σ-11))*(1-σ)) + ε) := by
  obtain ⟨C,hC,h⟩ := Montgomery.WrittenDensity.uniform_source_oct2_mixed_4 hε
  refine ⟨C,hC,?_⟩
  intro σ T hlo hhi hT F hF
  rw [← exact_count_identity σ T F hF]
  convert (h σ T hlo hhi hT) using 1
  all_goals ring_nf

/-- Verified recovered-family uniform quantifier order, separate from original analytic-route status. -/
theorem uniform_P31 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26 : ℝ) ≤ σ → σ ≤ (1 : ℝ) → 2 ≤ T →
      ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ _root_.riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt _root_.riemannZeta ρ : ℕ) : ℝ) ≤
        C * T ^ (((6/(σ+3))*(1-σ)) + ε) := by
  obtain ⟨C,hC,h⟩ := Montgomery.WrittenDensity.uniform_source_oct2_mixed_5 hε
  refine ⟨C,hC,?_⟩
  intro σ T hlo hhi hT F hF
  rw [← exact_count_identity σ T F hF]
  convert (h σ T hlo hhi hT) using 1
  all_goals ring_nf

/-- The endpoint count is zero because the critical strip itself is empty at cutoff one. -/
theorem count_at_one (T : ℝ) : zetaDensityCount 1 T = 0 := by
  have he : zetaZeroFinset 1 (-T) T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    have hh := mem_zetaDensityFinset.mp hρ
    exact (not_lt_of_ge hh.2.1) hh.1.2.2
  simp only [zetaDensityCount,zetaSlabCount,he,Finset.sum_empty]

end FinalDensitySurface
