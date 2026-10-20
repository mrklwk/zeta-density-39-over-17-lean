module
public import GeneralLargeGcdEnergy
public import DiscreteAdditiveEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Actual four-term additive energy, with no cardinality lower bound. -/
theorem discrete_energy_adjacent_unrestricted {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N → N ≤ T →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
      (∀ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖ ≤ 1) →
      0 < V → (∀ t ∈ W, V ≤ ‖GuthMaynard.Improvement.boundedPolynomial N a t‖) →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (discreteAdditiveEnergy W:ℝ) ≤ C*T^η*(N^4*(W.card:ℝ)/V^4+
        (N*(W.card:ℝ)^3+T*(W.card:ℝ)^((5:ℝ)/2)+
          N*T^((1:ℝ)/4)*(W.card:ℝ)^((31:ℝ)/12))/V^2) := by
  obtain ⟨C₀,hC₀,hrepro⟩ := discrete_additive_energy_reproducing
  obtain ⟨C₁,hC₁,hsmall⟩ := small_gcd_cubic_energy
  obtain ⟨C₂,hC₂,hlarge⟩ := large_gcd_adjacent_general hη
  refine ⟨(C₀*C₁)^2+2*C₀*C₂,by positivity,?_⟩
  intro T t₀ N hT hN hNT a W V ha hV hlargeW hW hsep
  have ht : 0 < T := by linarith
  by_cases he : W = ∅
  · subst W
    simp [discreteAdditiveEnergy]
  have hr : (0:ℝ) < W.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr he)
  let A := GuthMaynard.Improvement.sourceRatioIndices N
  let P := A ×ˢ A
  let F := fun p : ℕ × ℕ => ‖∑ t ∈ W, phase (pairRatio p) t‖^3
  let B := N*(W.card:ℝ)^3+T*(W.card:ℝ)^((5:ℝ)/2)+
    N*T^((1:ℝ)/4)*(W.card:ℝ)^((31:ℝ)/12)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hP : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      N < p.1 ∧ (p.1:ℝ) ≤ 2*N ∧ N < p.2 ∧ (p.2:ℝ) ≤ 2*N := by
    intro p hp
    obtain ⟨hp1,hp2⟩ := mem_product.mp hp
    obtain ⟨hl1,hu1⟩ := (GuthMaynard.Improvement.sourceRatioIndices_mem hN.le p.1).mp hp1
    obtain ⟨hl2,hu2⟩ := (GuthMaynard.Improvement.sourceRatioIndices_mem hN.le p.2).mp hp2
    exact ⟨by exact_mod_cast hN.trans hl1,by exact_mod_cast hN.trans hl2,hl1,hu1,hl2,hu2⟩
  have hsmall' := hsmall T t₀ N hT hN
    (P.filter (fun p => (pairGcd p:ℝ) < N^2/T)) (by
      intro p hp
      exact ⟨(hP p (mem_filter.mp hp).1).1,
        (hP p (mem_filter.mp hp).1).2.1,(hP p (mem_filter.mp hp).1).2.2.1,
        (hP p (mem_filter.mp hp).1).2.2.2.1,(hP p (mem_filter.mp hp).1).2.2.2.2.1,
        (hP p (mem_filter.mp hp).1).2.2.2.2.2,(mem_filter.mp hp).2⟩) W hW hsep
  let Q := P.filter (fun p => N^2/T ≤ (pairGcd p:ℝ))
  have hlarge' := hlarge T t₀ N hT hN hNT Q (by
    intro p hp
    obtain ⟨hp,hd⟩ := mem_filter.mp hp
    obtain ⟨h1,h2,hl1,hu1,hl2,hu2⟩ := hP p hp
    exact ⟨h1,h2,hl1,hu1,hl2,hu2,hd⟩) W hW hsep
  have hp5 : (W.card:ℝ)^((5:ℝ)/2)=(W.card:ℝ)*(W.card:ℝ)^((3:ℝ)/2) := by
    convert Real.rpow_add hr (1:ℝ) ((3:ℝ)/2) using 1 <;> norm_num
  have hp31 : (W.card:ℝ)^((31:ℝ)/12)=(W.card:ℝ)*(W.card:ℝ)^((19:ℝ)/12) := by
    convert Real.rpow_add hr (1:ℝ) ((19:ℝ)/12) using 1 <;> norm_num
  have hid : N*(W.card:ℝ)*((W.card:ℝ)^2+(T/N)*(W.card:ℝ)^((3:ℝ)/2)+
      T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12))=B := by
    dsimp [B]
    rw [hp5,hp31]
    field_simp
  have hlarge3 : (∑ p ∈ Q,F p) ≤ C₂*T^η*B := by
    calc
      _ ≤ ∑ p ∈ Q, (W.card:ℝ)*‖∑ t ∈ W,phase (pairRatio p) t‖^2 := by
        apply sum_le_sum
        intro p _
        have hn := rational_phase_sum_norm_le_card (pairRatio p) W
        dsimp only [F]
        nlinarith [mul_le_mul_of_nonneg_right hn (sq_nonneg ‖∑ t ∈ W,phase (pairRatio p) t‖)]
      _ = (W.card:ℝ)*(∑ p ∈ Q, ‖∑ t ∈ W,phase (pairRatio p) t‖^2) := by rw [mul_sum]
      _ ≤ (W.card:ℝ)*(C₂*T^η*N*((W.card:ℝ)^2+(T/N)*(W.card:ℝ)^((3:ℝ)/2)+
          T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12))) := by gcongr
      _ = C₂*T^η*(N*(W.card:ℝ)*((W.card:ℝ)^2+(T/N)*(W.card:ℝ)^((3:ℝ)/2)+
          T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12))) := by ring
      _ = _ := by rw [hid]
  have he : (∑ p ∈ P,F p) =
      (∑ p ∈ P.filter (fun p => (pairGcd p:ℝ) < N^2/T),F p)+(∑ p ∈ Q,F p) := by
    simpa only [Q,not_lt] using
      (sum_filter_add_sum_filter_not P (fun p => (pairGcd p:ℝ) < N^2/T) F).symm
  have hrep := hrepro N hN a W V ha hV.le hlargeW hsep
  have hpair : (∑ n ∈ A,∑ m ∈ A,‖∑ t ∈ W,phase ((n:ℝ)/m) t‖^3)=∑ p ∈ P,F p := by
    simp only [P,F,sum_product,pairRatio,Rat.cast_div,Rat.cast_natCast]
  rw [hpair,he] at hrep
  have hh : (discreteAdditiveEnergy W:ℝ)*V^2 ≤
      (C₀*C₁*N^2*Real.sqrt (W.card:ℝ))*Real.sqrt (discreteAdditiveEnergy W:ℝ)+
        C₀*C₂*T^η*B := by
    have hsum := mul_le_mul_of_nonneg_left (add_le_add hsmall' hlarge3) hC₀.le
    nlinarith
  have habs := discrete_energy_absorb (Nat.cast_nonneg (discreteAdditiveEnergy W)) hV hh
  have hsq : (C₀*C₁*N^2*Real.sqrt (W.card:ℝ))^2=(C₀*C₁)^2*N^4*(W.card:ℝ) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hr.le]
    ring
  rw [hsq] at habs
  have hpow : 1 ≤ T^η := Real.one_le_rpow hT.le hη.le
  have h₁ : 0 ≤ N^4*(W.card:ℝ)/V^4 := by positivity
  have h₂ : 0 ≤ B/V^2 := by positivity
  calc
    _ ≤ (C₀*C₁)^2*(N^4*(W.card:ℝ)/V^4)+(2*C₀*C₂)*T^η*(B/V^2) :=
      habs.trans_eq (by ring)
    _ ≤ (C₀*C₁)^2*T^η*(N^4*(W.card:ℝ)/V^4)+(2*C₀*C₂)*T^η*(B/V^2) := by
      gcongr
      nlinarith
    _ ≤ _ := by
      dsimp only [B]
      nlinarith [mul_nonneg (sq_nonneg (C₀*C₁)) (mul_nonneg (by positivity : 0 ≤ T^η) h₂),
        mul_nonneg (show 0 ≤ 2*C₀*C₂ by positivity) (mul_nonneg (by positivity : 0 ≤ T^η) h₁)]


end Montgomery.RationalMoment
