module
public import GuthMaynard.Improvement.ShortDensityUniform

@[expose] public section

open Finset MathCollab.Density
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- A finite grid uniformizes a fixed-sigma estimate on a closed interval,
provided the exponent has a one-sided Lipschitz bound there. No estimate
across a downward jump in the exponent is assumed. -/
theorem density_curve_uniform_on_interval {a b K : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hK : 0 < K)
    (hmod : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b → f x ≤ f y+K*(y-x))
    (hfixed : ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
        (zetaDensityCount σ T:ℝ) ≤ C*T^(f σ+ε))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, a ≤ σ → σ ≤ b → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(f σ+ε) := by
  classical
  have hd : 0 < b-a := sub_pos.mpr hab
  obtain ⟨n,hn⟩ := exists_nat_gt (2*K*(b-a)/ε)
  have hn0 : 0 < (n:ℝ) := (by positivity : 0 < 2*K*(b-a)/ε).trans hn
  have hmesh : K*((b-a)/(n:ℝ)) ≤ ε/2 := by
    have hh := (div_lt_iff₀ hε).mp hn
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have he : K*((b-a)/(n:ℝ))*2 = 2*K*(b-a)/(n:ℝ) := by ring
    rw [he]
    exact (div_le_iff₀ hn0).mpr (by linarith)
  let grid := fun j : Fin (n+1) => a+(j:ℕ)*(b-a)/(n:ℝ)
  have hg (j : Fin (n+1)) : a ≤ grid j ∧ grid j ≤ b := by
    have hj : (j:ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
    have hjr : ((j:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hj
    dsimp [grid]
    constructor
    · have hh : 0 ≤ ((j:ℕ):ℝ)*(b-a)/(n:ℝ) := by positivity
      linarith
    · have hh : ((j:ℕ):ℝ)*(b-a)/(n:ℝ) ≤ b-a :=
        (div_le_iff₀ hn0).mpr (by nlinarith)
      linarith
  have hex (j : Fin (n+1)) := hfixed (grid j) (hg j).1 (hg j).2 (ε/2) (by positivity)
  choose C hC hbound using hex
  let B : ℝ := 1+∑ j : Fin (n+1),C j
  have hsum : 0 ≤ ∑ j : Fin (n+1),C j := Finset.sum_nonneg (fun j _ => (hC j).le)
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro σ T hσ hσ' hT
  let u : ℝ := (σ-a)*(n:ℝ)/(b-a)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hun : u ≤ (n:ℝ) := (div_le_iff₀ hd).mpr (by nlinarith)
  have hjn : ⌊u⌋₊ ≤ n := by exact_mod_cast (Nat.floor_le hu).trans hun
  let j : Fin (n+1) := ⟨⌊u⌋₊,Nat.lt_succ_of_le hjn⟩
  have hjlow : grid j ≤ σ := by
    have hh := (le_div_iff₀ hd).mp (Nat.floor_le hu)
    have ht : (⌊u⌋₊:ℝ)*(b-a)/(n:ℝ) ≤ σ-a :=
      (div_le_iff₀ hn0).mpr (by simpa [u] using hh)
    dsimp [grid,j]
    linarith
  have hjgap : σ-grid j ≤ (b-a)/(n:ℝ) := by
    have hh := (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one u)
    apply (le_div_iff₀ hn0).mpr
    dsimp [grid,j]
    have he : (a+(⌊u⌋₊:ℝ)*(b-a)/(n:ℝ))*(n:ℝ) =
        a*(n:ℝ)+(⌊u⌋₊:ℝ)*(b-a) := by field_simp
    nlinarith [he]
  have hexp : f (grid j)+ε/2 ≤ f σ+ε := by
    have hm := hmod (grid j) σ (hg j).1 hjlow hσ'
    have hh := (mul_le_mul_of_nonneg_left hjgap hK.le).trans hmesh
    linarith
  have hmono : (zetaDensityCount σ T:ℝ) ≤ (zetaDensityCount (grid j) T:ℝ) := by
    exact_mod_cast zetaDensityCount_mono hjlow (le_refl T)
  have hCB : C j ≤ B := by
    have hh : C j ≤ ∑ i : Fin (n+1),C i :=
      Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ j)
    dsimp [B]
    linarith
  calc
    _ ≤ C j*T^(f (grid j)+ε/2) := hmono.trans (hbound j T hT)
    _ ≤ C j*T^(f σ+ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) (hC j).le
    _ ≤ B*T^(f σ+ε) := mul_le_mul_of_nonneg_right hCB (by positivity)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.density_curve_uniform_on_interval
