module
public import SampledAdditiveMoments
public import IntegerFourthMoment

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Distinct reduced fractions in an actual dyadic interval give the
required separated normalized Fourier frequencies. -/
theorem coprime_dyadic_cubic {T t₀ M : ℝ} (hT : 1 < T) (hM : 0 < M)
    (Q : Finset (ℕ × ℕ))
    (hQ : ∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
      M < q.1 ∧ (q.1:ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2:ℝ) ≤ 2*M)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) :
    (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^3) ≤
      (512*(1+12*Real.pi))*(T+16*Real.pi*M^2)*Real.sqrt (W.card:ℝ)*
        Real.sqrt (discreteAdditiveEnergy W:ℝ) := by
  let x : Q → ℝ := fun q => Real.log ((q.1.1:ℝ)/q.1.2)/(2*Real.pi)
  let δ : ℝ := 1/(16*Real.pi*M^2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hx (q : Q) : |x q| ≤ 1 := by
    obtain ⟨h1,h2,_,hl1,hu1,hl2,hu2⟩ := hQ q q.2
    have hh := dyadic_pair_log h1 h2 hl1 hu1 hl2 hu2
    simp only [pairRatio,Rat.cast_div,Rat.cast_natCast] at hh
    dsimp [x]
    rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have hs : Pairwise (fun p q : Q => δ ≤ |x p-x q|) := by
    intro p q hpq
    have hp := hQ p p.2
    have hq := hQ q q.2
    have hgap := rational_log_separation ⟨hp.1,hp.2.1,hp.2.2.1⟩
      ⟨hq.1,hq.2.1,hq.2.2.1⟩ (by exact fun he => hpq (Subtype.ext he))
      hp.2.2.2.2.2.2 hq.2.2.2.2.2.2
      (U := 2) ((div_le_iff₀ (by exact_mod_cast hp.2.1)).mpr (by linarith [hp.2.2.2.1,hp.2.2.2.2.2.1]))
      ((div_le_iff₀ (by exact_mod_cast hq.2.1)).mpr (by linarith [hq.2.2.2.1,hq.2.2.2.2.2.1]))
    dsimp [x,δ]
    rw [← sub_div,abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    convert hgap using 1; field_simp; ring
  have hh := sampled_character_cubic hT hδ W hW hsep x hx hs
  have he (q : Q) : ‖centeredCharacter W t₀ (x q)‖=‖∑ t ∈ W, phase (pairRatio q) t‖ := by
    dsimp only [x]
    rw [centered_character_norm]
    simp only [pairRatio,Rat.cast_div,Rat.cast_natCast]
  simp only [he] at hh
  rw [Finset.sum_coe_sort Q (fun q => ‖∑ t ∈ W, phase (pairRatio q) t‖^3)] at hh
  have hd : δ⁻¹=16*Real.pi*M^2 := by dsimp [δ]; rw [inv_div,div_one]
  rwa [hd] at hh

/-- Summing the small-gcd classes costs N^2, with no logarithmic or
subpower loss and with the original quadruple energy retained. -/
theorem small_gcd_cubic_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N →
      ∀ (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        N < p.1 ∧ (p.1:ℝ) ≤ 2*N ∧ N < p.2 ∧ (p.2:ℝ) ≤ 2*N ∧
        (pairGcd p:ℝ) < N^2/T) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^3) ≤
        C*N^2*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ) := by
  let C : ℝ := 512*(1+12*Real.pi)
  refine ⟨C*(1+32*Real.pi),by dsimp [C]; positivity,?_⟩
  intro T t₀ N hT hN P hP W hW hsep
  have hTp : 0 < T := by linarith
  have hgeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      N < p.1 ∧ (p.1:ℝ) ≤ 2*N ∧ N < p.2 ∧ (p.2:ℝ) ≤ 2*N := by
    intro p hp
    obtain ⟨h1,h2,hl1,hu1,hl2,hu2,_⟩ := hP p hp
    exact ⟨h1,h2,hl1,hu1,hl2,hu2⟩
  have hd (d : ℕ) (hd : d ∈ gcdValues P) : 0 < d ∧ (d:ℝ) < N^2/T := by
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hd
    exact ⟨Nat.gcd_pos_of_pos_left _ (hP p hp).1,(hP p hp).2.2.2.2.2.2⟩
  have hblock (d : ℕ) (hd' : d ∈ gcdValues P) :
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖^3) ≤
      C*(T+16*Real.pi*(N/d)^2)*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ) := by
    apply coprime_dyadic_cubic hT (by have := (hd d hd').1; positivity)
      (reducedFiber P d) _ W hW hsep
    intro q hq
    exact (reduced_fiber_bounds hgeom hq).2
  have hcount : (gcdValues P).card ≤ ⌊N^2/T⌋₊ := by
    apply le_trans (card_le_card (show gcdValues P ⊆ Icc 1 ⌊N^2/T⌋₊ from ?_))
      (by simp)
    intro d hd'
    exact mem_Icc.mpr ⟨(hd d hd').1,Nat.le_floor (hd d hd').2.le⟩
  have hsum : (∑ d ∈ gcdValues P, (T+16*Real.pi*(N/d)^2)) ≤ (1+32*Real.pi)*N^2 := by
    have hrec := nat_reciprocal_square_budget (gcdValues P) (fun d hd' => (hd d hd').1.ne')
    have hcount' : ((gcdValues P).card:ℝ)*T ≤ N^2 := by
      have hc : ((gcdValues P).card:ℝ) ≤ N^2/T :=
        (by exact_mod_cast hcount : ((gcdValues P).card:ℝ) ≤ ⌊N^2/T⌋₊).trans
          (Nat.floor_le (by positivity))
      exact (le_div_iff₀ hTp).mp hc
    have he : (∑ d ∈ gcdValues P, (T+16*Real.pi*(N/d)^2)) =
        ((gcdValues P).card:ℝ)*T+16*Real.pi*N^2*(∑ d ∈ gcdValues P, ((d:ℝ)^2)⁻¹) := by
      simp only [sum_add_distrib,sum_const,nsmul_eq_mul]
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro d _
      simp only [div_eq_mul_inv]
      ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hrec (by positivity : 0 ≤ 16*Real.pi*N^2)]
  rw [sum_by_gcd P (fun p hp => (hP p hp).1) (fun r : ℚ => ‖∑ t ∈ W, phase (r:ℝ) t‖^3)]
  calc
    _ ≤ ∑ d ∈ gcdValues P, C*(T+16*Real.pi*(N/d)^2)*Real.sqrt (W.card:ℝ)*
        Real.sqrt (discreteAdditiveEnergy W:ℝ) := sum_le_sum hblock
    _ = C*(∑ d ∈ gcdValues P, (T+16*Real.pi*(N/d)^2))*Real.sqrt (W.card:ℝ)*
        Real.sqrt (discreteAdditiveEnergy W:ℝ) := by simp only [sum_mul,mul_sum]
    _ ≤ C*((1+32*Real.pi)*N^2)*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ) := by
      have hC : 0 ≤ C := by dsimp [C]; positivity
      gcongr
    _ = _ := by ring

/-- The exact small-gcd contribution in the existing discrete energy
reduction is now bounded unconditionally. -/
theorem small_gcd_cubic_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      smallGcdCubicSum N T W ≤ C*N^2*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := small_gcd_cubic_energy
  refine ⟨C,hC,?_⟩
  intro T t₀ N hT hN W hW hsep
  unfold smallGcdCubicSum
  apply hbound T t₀ N hT hN _ _ W hW hsep
  intro p hp
  obtain ⟨hp,hg⟩ := mem_filter.mp hp
  obtain ⟨hp1,hp2⟩ := mem_product.mp hp
  obtain ⟨hl1,hu1⟩ := (GuthMaynard.Improvement.sourceRatioIndices_mem hN.le p.1).mp hp1
  obtain ⟨hl2,hu2⟩ := (GuthMaynard.Improvement.sourceRatioIndices_mem hN.le p.2).mp hp2
  exact ⟨by exact_mod_cast hN.trans hl1,by exact_mod_cast hN.trans hl2,hl1,hu1,hl2,hu2,hg⟩

end Montgomery.RationalMoment
