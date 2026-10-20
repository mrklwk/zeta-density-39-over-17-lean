module
public import RationalDyadicDifference

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Fixed dilations of an actual dyadic interval do not change the
undilated short-range hypothesis. All constants precede the lengths. -/
theorem coprime_dilated_dyadic_short_range {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M U : ℝ), 1 < T → 0 ≤ M → 0 ≤ U → M ≤ B*U →
      ∀ (Q : Finset (ℕ × ℕ)),
      (∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        M < q.1 ∧ (q.1 : ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2 : ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ), T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → U^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        C*T^η*U*(W.card : ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := rational_energy_interval_short_range hK hη
    (B := 2*B) (by linarith)
  refine ⟨C,hC,?_⟩
  intro T t₀ M U hT hM hU hMU Q hQ W hR hUR hW hsep
  rw [reduced_energy_eq_rational_energy Q (fun q hq => ⟨(hQ q hq).2.1,(hQ q hq).2.2.1⟩) W]
  apply hbound T t₀ U hT hU (Q.image pairRatio) _ W hR hUR hW hsep
  intro r hr
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hr
  obtain ⟨h1,h2,hc,hl1,hu1,hl2,hu2⟩ := hQ q hq
  refine ⟨div_pos (by exact_mod_cast h1) (by exact_mod_cast h2),?_,
    dyadic_pair_log h1 h2 hl1 hu1 hl2 hu2⟩
  rw [coprime_pair_den h2 hc]
  linarith

theorem dilated_dyadic_pair_energy_log {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M U : ℝ), 1 < T → 0 ≤ M → 0 ≤ U → M ≤ B*U →
      ∀ (N : ℕ) (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ N ∧
        M < p.1 ∧ (p.1 : ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ),
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → U^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*U*(W.card : ℝ)^2*(1+Real.log N) := by
  obtain ⟨C, hC, hbound⟩ := coprime_dilated_dyadic_short_range hK hη hB
  refine ⟨C, hC, ?_⟩
  intro T t₀ M U hT hM hU hMU N P hP W hR hUR hW hsep
  have hgeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      M < p.1 ∧ (p.1 : ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2*M := by
    intro p hp
    exact ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.2⟩
  have hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        (C*T^η*(W.card : ℝ)^2)*(U/d) := by
    intro d hd
    obtain ⟨p, hp, he⟩ := mem_image.mp hd
    have hdpos : 0 < d := he ▸ Nat.gcd_pos_of_pos_left p.2 (hP p hp).1
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    have hdiv : U/(d : ℝ) ≤ U := div_le_self hU hd1
    have hQ : ∀ q ∈ reducedFiber P d,
        0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        M/d < q.1 ∧ (q.1 : ℝ) ≤ 2*(M/d) ∧
        M/d < q.2 ∧ (q.2 : ℝ) ≤ 2*(M/d) := by
      intro q hq
      exact (reduced_fiber_bounds hgeom hq).2
    have hh := hbound T t₀ (M/d) (U/d) hT (by positivity) (by positivity)
      (by calc M/(d:ℝ) ≤ (B*U)/d := div_le_div_of_nonneg_right hMU (by positivity)
               _ = B*(U/d) := by ring) (reducedFiber P d) hQ W hR
      ((pow_le_pow_left₀ (by positivity) hdiv K).trans hUR)
      hW hsep
    convert hh using 1
    ring
  have hh := pair_energy_le_log P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2.1⟩) W
    (show 0 ≤ C*T^η*(W.card : ℝ)^2 by positivity) hU hblock
  convert hh using 1
  ring

/-- Full all-pair estimate for a fixed dilation; the power condition uses U. -/
theorem dilated_dyadic_pair_energy {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M U : ℝ), 1 < T → 0 ≤ M → 0 ≤ U → M ≤ B*U →
      ∀ (P : Finset (ℕ × ℕ)),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        M < p.1 ∧ (p.1 : ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2 : ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ), T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card → U^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*U*(W.card : ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := dilated_dyadic_pair_energy_log hK
    (show 0 < η/2 by positivity) hB
  let D : ℝ := 1+(4*B)^(η/2)/(η/2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C*D,by positivity,?_⟩
  intro T t₀ M U hT hM hU hMU P hP W hR hUR hW hsep
  have hTp : 0 < T := by linarith
  have h2M : 0 ≤ 2*M := by positivity
  have hP' : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ ⌊2*M⌋₊ ∧
      M < p.1 ∧ (p.1:ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2:ℝ) ≤ 2*M := by
    intro p hp
    exact ⟨(hP p hp).1,(hP p hp).2.1,
      (Nat.le_floor_iff h2M).mpr (hP p hp).2.2.2.1,(hP p hp).2.2⟩
  have hUT := short_length_le_twice_time hK hT W hUR hW hsep
  have hN : (⌊2*M⌋₊:ℝ) ≤ 4*B*T := (Nat.floor_le h2M).trans (by nlinarith)
  have hδ : 0 < η/2 := by positivity
  have h1 : 1 ≤ T^(η/2) := Real.one_le_rpow hT.le hδ.le
  have hlog : Real.log ⌊2*M⌋₊ ≤ ((4*B)^(η/2)*T^(η/2))/(η/2) := by
    calc
      _ ≤ (⌊2*M⌋₊:ℝ)^(η/2)/(η/2) := Real.log_natCast_le_rpow_div _ hδ
      _ ≤ (4*B*T)^(η/2)/(η/2) := by gcongr
      _ = _ := by rw [Real.mul_rpow (by positivity : 0 ≤ 4*B) hTp.le]
  have hl : 1+Real.log ⌊2*M⌋₊ ≤ D*T^(η/2) := by
    calc
      _ ≤ T^(η/2)+((4*B)^(η/2)*T^(η/2))/(η/2) := add_le_add h1 hlog
      _ = _ := by dsimp [D]; ring
  have hh := hbound T t₀ M U hT hM hU hMU ⌊2*M⌋₊ P hP' W hR hUR hW hsep
  have hp : T^(η/2)*T^(η/2)=T^η := by
    rw [← Real.rpow_add hTp]
    congr 1
    ring
  calc
    _ ≤ C*T^(η/2)*U*(W.card:ℝ)^2*(1+Real.log ⌊2*M⌋₊) := hh
    _ ≤ C*T^(η/2)*U*(W.card:ℝ)^2*(D*T^(η/2)) := by gcongr
    _ = C*D*(T^(η/2)*T^(η/2))*U*(W.card:ℝ)^2 := by ring
    _ = _ := by rw [hp]

/-- Arbitrary bounded coefficients on the actual dilated dyadic support. -/
theorem dilated_dyadic_dirichlet_difference {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ M U : ℝ), 1 < T → 0 ≤ M → 0 ≤ U → M ≤ B*U →
      ∀ (A : Finset ℕ), (∀ n ∈ A, 0 < n ∧ M < n ∧ (n:ℝ) ≤ 2*M) →
      ∀ (W : Finset ℝ), T^(((K:ℝ)+1)/(2*K+1)) ≤ W.card → U^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ∀ (a : ℕ → ℂ), (∀ n ∈ A, ‖a n‖ ≤ 1) →
      (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n*phase n (t-u)‖^2) ≤
        C*T^η*U*(W.card:ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := dilated_dyadic_pair_energy hK hη hB
  refine ⟨C,hC,?_⟩
  intro T t₀ M U hT hM hU hMU A hA W hR hUR hW hsep a ha
  have hP : ∀ p ∈ A ×ˢ A, 0 < p.1 ∧ 0 < p.2 ∧
      M < p.1 ∧ (p.1:ℝ) ≤ 2*M ∧ M < p.2 ∧ (p.2:ℝ) ≤ 2*M := by
    intro p hp
    obtain ⟨hp1,hp2⟩ := mem_product.mp hp
    exact ⟨(hA p.1 hp1).1,(hA p.2 hp2).1,(hA p.1 hp1).2.1,
      (hA p.1 hp1).2.2,(hA p.2 hp2).2⟩
  have hh := hbound T t₀ M U hT hM hU hMU (A ×ˢ A) hP W hR hUR hW hsep
  simp only [sum_product,pairRatio,Rat.cast_div,Rat.cast_natCast] at hh
  exact (dirichlet_difference_energy_le A (fun n hn => (hA n hn).1) W a ha).trans hh

end Montgomery.RationalMoment
