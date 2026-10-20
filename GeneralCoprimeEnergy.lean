module
public import GeneralRationalEnergy
public import RationalLargeGcdEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem coprime_dyadic_adjacent_general {K : ℕ} (hK : 1 ≤ K) {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ M : ℝ, 1 < T → 0 ≤ M → M ≤ B*T →
      ∀ Q : Finset (ℕ × ℕ),
      (∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        M < q.1 ∧ (q.1:ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2:ℝ) ≤ 2*M) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        C*T^η*(M*(W.card:ℝ)^2+M^2*(W.card:ℝ)^(2-1/(K:ℝ))+
          M*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
  obtain ⟨C,hC,hb⟩ := rational_energy_adjacent_unrestricted hK hη (B:=2*B) (by linarith)
  refine ⟨4*C,by positivity,?_⟩
  intro T t₀ M hT hM hMT Q hQ W hW hsep
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
      (Q.image pairRatio) hrat W hW hsep
    calc
      _ ≤ C*T^η*((⌊2*M⌋₊:ℝ)*(W.card:ℝ)^2+
          (⌊2*M⌋₊:ℝ)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
          (⌊2*M⌋₊:ℝ)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := hh
      _ ≤ C*T^η*((2*M)*(W.card:ℝ)^2+(2*M)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
          (2*M)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by gcongr
      _ ≤ _ := by
        have h1 : 0 ≤ M*(W.card:ℝ)^2 := by positivity
        have h3 : 0 ≤ M*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) := by positivity
        have hi : (2*M)*(W.card:ℝ)^2+(2*M)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
            (2*M)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) ≤
            4*(M*(W.card:ℝ)^2+M^2*(W.card:ℝ)^(2-1/(K:ℝ))+
              M*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by nlinarith
        exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)
  · rw [not_nonempty_iff_eq_empty.mp he,sum_empty]
    positivity


end Montgomery.RationalMoment
