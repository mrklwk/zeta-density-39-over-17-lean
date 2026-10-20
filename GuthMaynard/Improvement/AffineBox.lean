module
public import GuthMaynard.Improvement.AffineFiniteCover

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Precise closed real dyadic box, retaining both nonzero slope signs. -/
def InAffineBox (B Q C₀ : ℝ) (p : ℤ × (ℤ × ℤ)) : Prop :=
  B ≤ |(p.1:ℝ)| ∧ |(p.1:ℝ)| ≤ 2*B ∧ Q ≤ (p.2.1:ℝ) ∧
    (p.2.1:ℝ) ≤ 2*Q ∧ |(p.2.2:ℝ)| ≤ C₀*B

def twoShell (B : ℝ) (i : Bool) : ℕ := if i then 2*⌊B⌋₊ else ⌊B⌋₊

theorem twoShell_pos {B : ℝ} (hB : 1 ≤ B) (i : Bool) : 0 < twoShell B i := by
  have h := Nat.floor_pos.mpr hB
  cases i <;> simp [twoShell] <;> omega

theorem twoShell_le {B : ℝ} (hB : 1 ≤ B) (i : Bool) : (twoShell B i:ℝ) ≤ 2*B := by
  have h := Nat.floor_le (show 0 ≤ B by linarith)
  cases i <;> simp [twoShell] <;> linarith

/-- The full finite real dyadic box is controlled with four native boxes,
including arbitrary fixed translation allowance. Denominators may exceed
slopes; the right side uses max B Q. -/
theorem affine_finite_box (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T B Q : ℝ) (f : 𝓢(ℝ, ℝ)) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ B → 1 ≤ Q → max B Q ≤ T^4 →
      (∀ x, 0 ≤ f x) → GMAffineSourceSupported f → FourierSupFamily D T f →
      (∀ p ∈ S, InAffineBox B Q C₀ p) →
      affineIndexIntegral f S ≤ C*T^ε*
        ((max B Q)^2*Q^4*(∫ x, f x)^2+(max B Q)*Q^3*(∫ x, f x^2)) := by
  obtain ⟨C,hC,h⟩ := mixed_affine_real_scales D hD (C₀+2) (by linarith) hε
  refine ⟨16*C,by positivity,?_⟩
  intro T B Q f S hT hB hQ hRT hf hs hp hbox
  let M₃ := ⌈C₀*B+1⌉₊
  have hM₃ : 0 < M₃ := Nat.ceil_pos.mpr (by positivity)
  have hM₃r : (M₃:ℝ) ≤ (C₀+2)*max B Q := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ C₀*B+1 by positivity)
    have hBmax := le_max_left B Q
    have hr1 : 1 ≤ max B Q := hB.trans hBmax
    have hmul := mul_le_mul_of_nonneg_left hBmax hC₀
    dsimp only [M₃]
    nlinarith only [hh,hr1,hmul]
  have h₁bound : ∀ i : Bool, (twoShell B i:ℝ) ≤ (C₀+2)*max B Q := by
    intro i
    have hb := twoShell_le hB i
    have hbm := le_max_left B Q
    have hm : 0 ≤ C₀*max B Q := by positivity
    nlinarith only [hb,hbm,hm]
  have h₂bound : ∀ i : Bool, (twoShell Q i:ℝ) ≤ (C₀+2)*Q := by
    intro i
    have hb := twoShell_le hQ i
    have hm : 0 ≤ C₀*Q := by positivity
    nlinarith only [hb,hm]
  let A : Finset (Bool × Bool) := Finset.univ
  have hcover : ∀ p ∈ S, ∃ i ∈ A,
      p ∈ gmAffineIndexSet (twoShell B i.1) (twoShell Q i.2) M₃ := by
    intro p hpS
    obtain ⟨hb1,hb2,hq1,hq2,hd⟩ := hbox p hpS
    have hb := real_signed_two_shells hB hb1 hb2
    have hq := real_dyadic_two_shells hQ hq1 hq2
    have hdM : p.2.2 ∈ gmAffineCentralShell M₃ := by
      have hc : C₀*B+1 ≤ (M₃:ℝ) := Nat.le_ceil _
      have hMp : (0:ℝ) < M₃ := by exact_mod_cast hM₃
      have hadd : |(p.2.2:ℝ)| ≤ 8*(M₃:ℝ) := by linarith only [hd,hc,hMp]
      have ha := abs_le.mp hadd
      apply mem_gmAffineCentralShell.mpr
      constructor
      · exact_mod_cast ha.1
      · exact_mod_cast ha.2
    rcases hb with hb | hb <;> rcases hq with hq | hq
    · exact ⟨(false,false),Finset.mem_univ _,mem_gmAffineIndexSet.mpr ⟨hb,hq,hdM⟩⟩
    · exact ⟨(false,true),Finset.mem_univ _,mem_gmAffineIndexSet.mpr ⟨hb,hq,hdM⟩⟩
    · exact ⟨(true,false),Finset.mem_univ _,mem_gmAffineIndexSet.mpr ⟨hb,hq,hdM⟩⟩
    · exact ⟨(true,true),Finset.mem_univ _,mem_gmAffineIndexSet.mpr ⟨hb,hq,hdM⟩⟩
  have hcov := affine_integral_le_cover f hf S A (fun i => twoShell B i.1)
    (fun i => twoShell Q i.2) (fun _ => M₃)
    (fun i _ => twoShell_pos hB i.1) (fun i _ => twoShell_pos hQ i.2) hcover
  have hpoint : ∀ i ∈ A, gmAffineTransformIntegral f (twoShell B i.1) (twoShell Q i.2) M₃ ≤
      C*T^ε*((max B Q)^2*Q^4*(∫ x, f x)^2+(max B Q)*Q^3*(∫ x, f x^2)) := by
    intro i hi
    exact h T (max B Q) Q f (twoShell B i.1) (twoShell Q i.2) M₃ hT hQ
      (le_max_right B Q) hRT hf hs hp (twoShell_pos hB i.1) (twoShell_pos hQ i.2) hM₃
      (h₁bound i.1) (h₂bound i.2) hM₃r
  have hsum := Finset.sum_le_sum hpoint
  have hcard : A.card = 4 := by simp [A]
  rw [Finset.sum_const,hcard] at hsum
  rw [hcard] at hcov
  norm_num only [Nat.cast_ofNat,nsmul_eq_mul] at hsum hcov
  exact hcov.trans (by nlinarith only [hsum])

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.twoShell_pos
#print axioms GuthMaynard.Improvement.twoShell_le
#print axioms GuthMaynard.Improvement.affine_finite_box
