module
public import GeneralCoprimeEnergy
public import RationalLargeGcdEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Large-gcd pair energy with the two extra adjacent-moment terms. The
short-range height condition (T/X)^K<=R is absent. -/
theorem large_gcd_adjacent_general {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 1 < T → 0 < X → X ≤ T →
      ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        X < p.1 ∧ (p.1:ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2:ℝ) ≤ 2*X ∧
        X^2/T ≤ (pairGcd p:ℝ)) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*X*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
          T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by
  obtain ⟨C,hC,hb⟩ := coprime_dyadic_adjacent_general (K:=2) (by norm_num) (show 0 < η/2 by positivity) (B:=1) (by norm_num)
  let L : ℝ := 1+4^(η/2)/(η/2)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C*L,by positivity,?_⟩
  intro T t₀ X hT hX hXT P hP W hW hsep
  have ht : 0 < T := by linarith
  have hgeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      X < p.1 ∧ (p.1:ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2:ℝ) ≤ 2*X := by
    intro p hp
    obtain ⟨h1,h2,hl1,hu1,hl2,hu2,_⟩ := hP p hp
    exact ⟨h1,h2,hl1,hu1,hl2,hu2⟩
  have hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        (C*T^(η/2)*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
          T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)))*(X/d) := by
    intro d hd
    obtain ⟨p,hp,he⟩ := mem_image.mp hd
    have hd0 : 0 < d := he ▸ Nat.gcd_pos_of_pos_left _ (hP p hp).1
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd0
    have hdD : X^2/T ≤ (d:ℝ) := he ▸ (hP p hp).2.2.2.2.2.2
    have hdiv : X/(d:ℝ) ≤ T/X := by
      have hh := div_le_div_of_nonneg_left hX.le (show 0 < X^2/T by positivity) hdD
      have heq : X/(X^2/T)=T/X := by field_simp
      exact hh.trans_eq heq
    have hdivT : X/(d:ℝ) ≤ T :=
      (div_le_self hX.le hd1).trans hXT
    have hQ : ∀ q ∈ reducedFiber P d,
        0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        X/d < q.1 ∧ (q.1:ℝ) ≤ 2*(X/d) ∧ X/d < q.2 ∧ (q.2:ℝ) ≤ 2*(X/d) :=
      fun q hq => (reduced_fiber_bounds hgeom hq).2
    have hh := hb T t₀ (X/d) hT (by positivity) (by simpa using hdivT) (reducedFiber P d) hQ
      W hW hsep
    norm_num at hh
    have hm : (X/(d:ℝ))^2 ≤ (T/X)*(X/d) := by
      have hm := mul_le_mul_of_nonneg_right hdiv (show 0 ≤ X/(d:ℝ) by positivity)
      nlinarith only [hm]
    apply hh.trans
    have hm' := mul_le_mul_of_nonneg_right hm (show 0 ≤ (W.card:ℝ)^((3:ℝ)/2) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hm' (show 0 ≤ C*T^(η/2) by positivity)
    nlinarith only [hh']
  have h2X : 0 ≤ 2*X := by positivity
  have hpN : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ ⌊2*X⌋₊ := by
    intro p hp
    exact ⟨(hP p hp).1,(Nat.le_floor_iff h2X).mpr (hP p hp).2.2.2.1⟩
  have hh := pair_energy_le_log P hpN W (show 0 ≤ C*T^(η/2)*
      ((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
        T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) by positivity) hX.le hblock
  have hN : (⌊2*X⌋₊:ℝ) ≤ 4*T := (Nat.floor_le h2X).trans (by linarith)
  have hl := logarithmic_height_loss hT.le (show 0 < η/2 by positivity) ⌊2*X⌋₊ hN
  change 1+Real.log ⌊2*X⌋₊ ≤ L*T^(η/2) at hl
  have hp : T^(η/2)*T^(η/2)=T^η := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  calc
    _ ≤ (C*T^(η/2)*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
        T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)))*X*(1+Real.log ⌊2*X⌋₊) := hh
    _ ≤ (C*T^(η/2)*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
        T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)))*X*(L*T^(η/2)) := by gcongr
    _ = C*L*(T^(η/2)*T^(η/2))*X*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
        T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by ring
    _ = _ := by rw [hp]

end Montgomery.RationalMoment
