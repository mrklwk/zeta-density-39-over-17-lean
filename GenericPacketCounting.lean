module
public import Mathlib
public import MathCollab.Density.Stronger.AtkinsonHeightCover

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.CriticalPeak
open MathCollab.Density.Stronger

/-- Physical subdivision length for a packet with positive length exponent. -/
def absorptionLength (k l A H G Y : ℝ) : ℝ :=
  (Y^2/(4*A*H^(l-k)*G^(1+k-2*l)))^(1/k)

theorem absorptionLength_pos {k l A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y) :
    0 < absorptionLength k l A H G Y := by
  unfold absorptionLength
  positivity

theorem absorptionLength_absorbs {k l A H G Y : ℝ}
    (hk : 0 < k) (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) :
    2*A*((absorptionLength k l A H G Y)^k*H^(l-k)*G^(1+k-2*l)) ≤ Y^2 := by
  have hp : 0 ≤ Y^2/(4*A*H^(l-k)*G^(1+k-2*l)) := by positivity
  unfold absorptionLength
  rw [← Real.rpow_mul hp, one_div_mul_cancel hk.ne', Real.rpow_one]
  have he : 2*A*((Y^2/(4*A*H^(l-k)*G^(1+k-2*l)))*H^(l-k)*G^(1+k-2*l)) =
      Y^2/2 := by
    have hHp : H^(l-k) ≠ 0 := (Real.rpow_pos_of_pos hH _).ne'
    have hGp : G^(1+k-2*l) ≠ 0 := (Real.rpow_pos_of_pos hG _).ne'
    field_simp
    ring
  rw [he]
  nlinarith [sq_nonneg Y]

theorem card_le_of_quadratic_packet {A H G Y X : ℝ} {W : Finset ℝ} {f : ℝ → ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hG : 0 < G) (hY : 0 < Y)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : (∑ t ∈ W, f t)^2 ≤ A*((W.card:ℝ)*H/G+(W.card:ℝ)^2*X))
    (habsorb : 2*A*X ≤ Y^2) :
    (W.card:ℝ) ≤ 2*A*H/(G*Y^2) := by
  by_cases hW : W.Nonempty
  · have hR : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
    have hsum : (W.card:ℝ)*Y ≤ ∑ t ∈ W, f t := by
      simpa using Finset.sum_le_sum hlarge
    have hsq := (pow_le_pow_left₀ (by positivity : 0 ≤ (W.card:ℝ)*Y) hsum 2).trans hpacket
    have hhalf := mul_le_mul_of_nonneg_right habsorb (sq_nonneg (W.card:ℝ))
    have hquad : (W.card:ℝ)*((W.card:ℝ)*Y^2) ≤ (W.card:ℝ)*(2*A*(H/G)) := by
      ring_nf at hsq hhalf ⊢
      nlinarith
    have hc := (mul_le_mul_iff_right₀ hR).mp hquad
    apply (le_div_iff₀ (mul_pos hG (sq_pos_of_pos hY))).2
    have he := (le_div_iff₀ hG).mp (show (W.card:ℝ)*Y^2 ≤ (2*A*H)/G by
      convert hc using 1; ring)
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hW]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

theorem covered_card_budget {k l A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y) :
    ((Nat.floor (H/absorptionLength k l A H G Y)+1:ℕ):ℝ)*(2*A*H/(G*Y^2)) ≤
      2*A*H/(G*Y^2)+(H/absorptionLength k l A H G Y)*(2*A*H/(G*Y^2)) := by
  have hL := absorptionLength_pos (k := k) (l := l) hA hH hG hY
  have hfloor := Nat.floor_le (div_nonneg hH.le hL.le)
  have hc : ((Nat.floor (H/absorptionLength k l A H G Y)+1:ℕ):ℝ) ≤
      H/absorptionLength k l A H G Y+1 := by
    push_cast
    linarith
  calc
    _ ≤ (H/absorptionLength k l A H G Y+1)*(2*A*H/(G*Y^2)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

/-- The generic subdivision lemma preserves the physical interval and packet powers. -/
theorem card_le_of_local_packets {k l A H G Y : ℝ}
    {W : Finset ℝ} {f : ℝ → ℝ}
    (hk : 0 < k) (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ B : ℝ, (∀ t ∈ U, B ≤ t ∧ t ≤ B+absorptionLength k l A H G Y) →
        (∑ t ∈ U, f t)^2 ≤ A*((U.card:ℝ)*H/G+(U.card:ℝ)^2*
          ((absorptionLength k l A H G Y)^k*H^(l-k)*G^(1+k-2*l)))) :
    (W.card:ℝ) ≤ 2*A*H/(G*Y^2)+
      (H/absorptionLength k l A H G Y)*(2*A*H/(G*Y^2)) := by
  let L := absorptionLength k l A H G Y
  have hL : 0 < L := absorptionLength_pos hA hH hG hY
  have hfiber (j : ℕ) : ((atkinsonHeightFiber H L W j).card:ℝ) ≤ 2*A*H/(G*Y^2) := by
    have hsub := atkinsonHeightFiber_subset H L W j
    have hlocal := atkinsonHeightFiber_interval j hL (fun t ht => (hrange t ht).1)
    have hp := hpacket (atkinsonHeightFiber H L W j) hsub (H+(j:ℝ)*L) hlocal
    exact card_le_of_quadratic_packet hA hH.le hG hY
      (fun t ht => hlarge t (hsub ht)) hp (absorptionLength_absorbs hk hA hH hG)
  have hc := atkinson_card_le_of_height_fibers hL
    (fun t ht => (hrange t ht).2) (fun j _ => hfiber j)
  exact hc.trans (covered_card_budget hA hH hG hY)

/-- Exact dependence on all four positive physical parameters. -/
theorem absorptionLength_eq {k l A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y) :
    absorptionLength k l A H G Y =
      Y^(2/k)/(4^(1/k)*A^(1/k)*H^((l-k)/k)*G^((1+k-2*l)/k)) := by
  unfold absorptionLength
  rw [Real.div_rpow (sq_nonneg Y) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ 4*A*H^(l-k)) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ 4*A) (by positivity),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hA.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hY.le,
    ← Real.rpow_mul hH.le, ← Real.rpow_mul hG.le]
  congr 2 <;> ring_nf

/-- The subdivision term has exactly the general exponent-pair powers. -/
theorem subdivision_term_eq {k l A H G Y : ℝ}
    (hk : 0 < k) (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y) :
    (H/absorptionLength k l A H G Y)*(2*A*H/(G*Y^2)) =
      2*4^(1/k)*A^(1+1/k)*H^(1+l/k)/(G^((2*l-1)/k)*Y^(2+2/k)) := by
  have hAp : A^(1/k) ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
  have hHp : H^((l-k)/k) ≠ 0 := (Real.rpow_pos_of_pos hH _).ne'
  have hGp : G^((1+k-2*l)/k) ≠ 0 := (Real.rpow_pos_of_pos hG _).ne'
  have hYp : Y^(2/k) ≠ 0 := (Real.rpow_pos_of_pos hY _).ne'
  have ha : A^(1+1/k) = A*A^(1/k) := by rw [Real.rpow_add hA,Real.rpow_one]
  have hh : H^(1+l/k) = H^2*H^((l-k)/k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hH]
    congr 1
    field_simp [hk.ne']
    ring
  have hg : G^((2*l-1)/k)*G^((1+k-2*l)/k) = G := by
    rw [← Real.rpow_add hG]
    have he : (2*l-1)/k+(1+k-2*l)/k = 1 := by
      field_simp [hk.ne']
      ring
    rw [he,Real.rpow_one]
  have hy : Y^(2+2/k) = Y^2*Y^(2/k) := by
    rw [Real.rpow_add hY, Real.rpow_two]
  rw [absorptionLength_eq hA hH hG hY,ha,hh,hy]
  have h4 : (4:ℝ)^(1/k) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hg' : G^((2*l-1)/k) = G/G^((1+k-2*l)/k) :=
    (eq_div_iff hGp).mpr hg
  rw [hg']
  field_simp

/-- The complete generic finite count, retaining both terms. -/
theorem card_le_two_powers {k l A H G Y : ℝ}
    {W : Finset ℝ} {f : ℝ → ℝ}
    (hk : 0 < k) (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ B : ℝ, (∀ t ∈ U, B ≤ t ∧ t ≤ B+absorptionLength k l A H G Y) →
        (∑ t ∈ U, f t)^2 ≤ A*((U.card:ℝ)*H/G+(U.card:ℝ)^2*
          ((absorptionLength k l A H G Y)^k*H^(l-k)*G^(1+k-2*l)))) :
    (W.card:ℝ) ≤ 2*A*H/(G*Y^2)+
      2*4^(1/k)*A^(1+1/k)*H^(1+l/k)/(G^((2*l-1)/k)*Y^(2+2/k)) := by
  have h := card_le_of_local_packets hk hA hH hG hY hrange hlarge hpacket
  rwa [subdivision_term_eq hk hA hH hG hY] at h


/-- Allocate the packet loss before the physical height is quantified. -/
theorem count_exponent_budget {k l D H G Y ν : ℝ}
    (hk : 0 < k) (hD : 0 ≤ D) (hH : 1 ≤ H) (hG : 0 < G)
    (hY : 0 < Y) (hν : 0 ≤ ν) :
    2*(D*H^(ν/(1+1/k)))*H/(G*Y^2)+
      2*4^(1/k)*(D*H^(ν/(1+1/k)))^(1+1/k)*H^(1+l/k)/
        (G^((2*l-1)/k)*Y^(2+2/k)) ≤
      (2*D+2*4^(1/k)*D^(1+1/k))*H^ν*
        (H/(G*Y^2)+H^(1+l/k)/(G^((2*l-1)/k)*Y^(2+2/k))) := by
  have hH0 : 0 < H := by linarith
  have hq : 0 < 1+1/k := by positivity
  have hq1 : 1 ≤ 1+1/k := le_add_of_nonneg_right (by positivity)
  have hp : H^(ν/(1+1/k)) ≤ H^ν :=
    Real.rpow_le_rpow_of_exponent_le hH (div_le_self hν hq1)
  have he : (D*H^(ν/(1+1/k)))^(1+1/k) = D^(1+1/k)*H^ν := by
    rw [Real.mul_rpow hD (by positivity), ← Real.rpow_mul hH0.le,
      div_mul_cancel₀ _ hq.ne']
  rw [he]
  calc
    _ ≤ 2*(D*H^ν)*H/(G*Y^2)+
        2*4^(1/k)*(D^(1+1/k)*H^ν)*H^(1+l/k)/
          (G^((2*l-1)/k)*Y^(2+2/k)) := by
      apply add_le_add _ le_rfl
      gcongr
    _ ≤ _ := by
      have hx : 0 ≤ 2*D*H^ν*(H^(1+l/k)/(G^((2*l-1)/k)*Y^(2+2/k))) := by positivity
      have hy : 0 ≤ 2*4^(1/k)*D^(1+1/k)*H^ν*(H/(G*Y^2)) := by positivity
      ring_nf at hx hy ⊢
      nlinarith

end Montgomery.CriticalPeak
