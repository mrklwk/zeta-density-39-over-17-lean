module
public import AdjacentRationalEnergy
public import RationalLargeGcdEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem coprime_dyadic_adjacent_second {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ M : ℝ, 1 < T → 0 ≤ M → M ≤ T →
      ∀ Q : Finset (ℕ × ℕ),
      (∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        M < q.1 ∧ (q.1:ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2:ℝ) ≤ 2*M) →
      ∀ W : Finset ℝ, T^((5:ℝ)/9) ≤ W.card → (W.card:ℝ)^3 ≤ T^2 →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        C*T^η*(M*(W.card:ℝ)^2+M^2*(W.card:ℝ)^((3:ℝ)/2)+
          M*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by
  obtain ⟨C,hC,hb⟩ := rational_energy_adjacent_second hη
  refine ⟨4*C,by positivity,?_⟩
  intro T t₀ M hT hM hMT Q hQ W hR hRT hW hsep
  by_cases he : Q.Nonempty
  · obtain ⟨q,hq⟩ := he
    have h2M : 0 ≤ 2*M := by positivity
    have hf : (⌊2*M⌋₊:ℝ) ≤ 2*M := Nat.floor_le h2M
    have hH : 1 ≤ ⌊2*M⌋₊ :=
      (show 1 ≤ q.2 from (hQ q hq).2.1).trans
        ((Nat.le_floor_iff h2M).mpr (hQ q hq).2.2.2.2.2.2)
    have hrat : ∀ r ∈ Q.image pairRatio,
        0 < r ∧ r.den ≤ ⌊2*M⌋₊ ∧ |Real.log (r:ℝ)| ≤ 1 := by
      intro r hr
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hr
      obtain ⟨hp1,hp2,hcop,hl1,hu1,hl2,hu2⟩ := hQ p hp
      refine ⟨div_pos (by exact_mod_cast hp1) (by exact_mod_cast hp2),?_,
        dyadic_pair_log hp1 hp2 hl1 hu1 hl2 hu2⟩
      rw [coprime_pair_den hp2 hcop]
      exact (Nat.le_floor_iff h2M).mpr hu2
    rw [reduced_energy_eq_rational_energy Q (fun p hp => ⟨(hQ p hp).2.1,(hQ p hp).2.2.1⟩) W]
    have hh := hb T t₀ hT ⌊2*M⌋₊ hH (hf.trans (by linarith))
      (Q.image pairRatio) hrat W hR hRT hW hsep
    calc
      _ ≤ C*T^η*((⌊2*M⌋₊:ℝ)*(W.card:ℝ)^2+
          (⌊2*M⌋₊:ℝ)^2*(W.card:ℝ)^((3:ℝ)/2)+
          (⌊2*M⌋₊:ℝ)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := hh
      _ ≤ C*T^η*((2*M)*(W.card:ℝ)^2+(2*M)^2*(W.card:ℝ)^((3:ℝ)/2)+
          (2*M)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by gcongr
      _ ≤ _ := by
        have h1 : 0 ≤ M*(W.card:ℝ)^2 := by positivity
        have h3 : 0 ≤ M*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12) := by positivity
        have hi : (2*M)*(W.card:ℝ)^2+(2*M)^2*(W.card:ℝ)^((3:ℝ)/2)+
            (2*M)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12) ≤
            4*(M*(W.card:ℝ)^2+M^2*(W.card:ℝ)^((3:ℝ)/2)+
              M*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by nlinarith
        exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)
  · rw [not_nonempty_iff_eq_empty.mp he,sum_empty]
    positivity

/-- Large-gcd pair energy with the two extra adjacent-moment terms. The
short-range height condition (T/X)^K<=R is absent. -/
theorem large_gcd_adjacent_pair {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 1 < T → 0 < X → X ≤ T →
      ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        X < p.1 ∧ (p.1:ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2:ℝ) ≤ 2*X ∧
        X^2/T ≤ (pairGcd p:ℝ)) →
      ∀ W : Finset ℝ, T^((5:ℝ)/9) ≤ W.card → (W.card:ℝ)^3 ≤ T^2 →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*X*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
          T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by
  obtain ⟨C,hC,hb⟩ := coprime_dyadic_adjacent_second (show 0 < η/2 by positivity)
  let L : ℝ := 1+4^(η/2)/(η/2)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C*L,by positivity,?_⟩
  intro T t₀ X hT hX hXT P hP W hR hRT hW hsep
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
    have hh := hb T t₀ (X/d) hT (by positivity) hdivT (reducedFiber P d) hQ
      W hR hRT hW hsep
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
