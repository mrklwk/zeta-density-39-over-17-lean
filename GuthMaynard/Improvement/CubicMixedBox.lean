module
public import GuthMaynard.Improvement.CubicStripIntegral
public import GuthMaynard.Improvement.MixedMaskedAffine
public import GuthMaynard.Improvement.InverseRatioIntegral
public import GuthMaynard.Improvement.MaskedBox

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

def stripAffineIndex (m : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) := (-m.1,m.2.1,-m.2.2)
def stripInverseIndex (m : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) := (-m.2.2,m.2.1,-m.1)
def InCubicBox (B K D : ℝ) (m : ℤ × (ℤ × ℤ)) : Prop :=
  B ≤ |(m.1:ℝ)| ∧ |(m.1:ℝ)| ≤ 2*B ∧ K ≤ (m.2.1:ℝ) ∧
    (m.2.1:ℝ) ≤ 2*K ∧ D ≤ |(m.2.2:ℝ)| ∧ |(m.2.2:ℝ)| ≤ 2*D

theorem stripAffineIndex_injective : Function.Injective stripAffineIndex := by
  intro m n h
  have h1 := congrArg (fun p : ℤ × (ℤ × ℤ) => p.1) h
  have h2 := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.1) h
  have h3 := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.2) h
  simp only [stripAffineIndex,neg_inj] at h1 h2 h3
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem stripInverseIndex_injective : Function.Injective stripInverseIndex := by
  intro m n h
  have h1 := congrArg (fun p : ℤ × (ℤ × ℤ) => p.1) h
  have h2 := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.1) h
  have h3 := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.2) h
  simp only [stripInverseIndex,neg_inj] at h1 h2 h3
  exact Prod.ext h3 (Prod.ext h2 h1)

theorem stripAffine_sum (S : Finset (ℤ × (ℤ × ℤ))) (F : ℝ → ℝ) (v : ℝ) :
    (∑ p ∈ S.image stripAffineIndex, gmAffineTerm F p.1 p.2.1 p.2.2 v) =
      ∑ m ∈ S, F (stripCenter m v) := by
  rw [Finset.sum_image (fun _ _ _ _ h => stripAffineIndex_injective h)]
  apply Finset.sum_congr rfl
  intro m _
  unfold gmAffineTerm stripAffineIndex stripCenter
  push_cast
  congr 1
  ring

theorem stripInverse_sum (S : Finset (ℤ × (ℤ × ℤ))) (F : ℝ → ℝ) (v : ℝ) :
    (∑ p ∈ S.image stripInverseIndex, gmAffineTerm F p.1 p.2.1 p.2.2 v) =
      ∑ m ∈ S, F (-((m.2.2:ℝ)*v+(m.1:ℝ))/(m.2.1:ℝ)) := by
  rw [Finset.sum_image (fun _ _ _ _ h => stripInverseIndex_injective h)]
  apply Finset.sum_congr rfl
  intro m _
  unfold gmAffineTerm stripInverseIndex
  push_cast
  congr 1
  ring

theorem finite_affine_memLp (F : 𝓢(ℝ, ℝ)) (S : Finset (ℤ × (ℤ × ℤ)))
    (hS : ∀ p ∈ S, p.1 ≠ 0 ∧ p.2.1 ≠ 0) :
    MemLp (fun v => ∑ p ∈ S, gmAffineTerm F p.1 p.2.1 p.2.2 v) 2 := by
  apply memLp_finsetSum
  intro p hp
  have hf2 := (memLp_two_iff_integrable_sq F.continuous.aestronglyMeasurable).mp (F.memLp 2)
  have hm : Measurable (gmAffineTerm F p.1 p.2.1 p.2.2) := by
    unfold gmAffineTerm
    fun_prop
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    (integrable_gmAffineTerm_sq hf2 (hS p hp).1 (hS p hp).2)

/-- Both actual affine energies, including inverse ratio, derived from the
mixed theorem with exact index injections and ordinary compact input. -/
theorem cubic_mixed_energies (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K B D δ : ℝ) (r : ℝ → ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ K → K ≤ R → 1 ≤ B → B ≤ R → 1 ≤ D → D ≤ R → R ≤ T^4 →
      0 < δ → δ ≤ 1 → δ ≤ c/4 → δ⁻¹ ≤ T → Measurable r →
      Integrable (fun x => r x^2) → Integrable (fun x => r x^4) →
      (∀ x, x ∉ Icc c d → r x = 0) → (∀ m ∈ S, InCubicBox B K D m) →
      let F := squareSmoothing (scaledKernel compactKernel δ) r
      let E := C*T^ε*(R^2*K^4*(∫ x, r x^2)^2+R*K^3*(∫ x, r x^4))
      IntegrableOn (fun v => (∑ m ∈ S, F (stripCenter m v))^2) (Icc a b) ∧
      IntegrableOn (fun v => (∑ m ∈ S, F (stripCenter m v/v))^2) (Icc a b) ∧
      (∫ v in Icc a b, (∑ m ∈ S, F (stripCenter m v))^2) ≤ E ∧
      (∫ v in Icc a b, (∑ m ∈ S, F (stripCenter m v/v))^2) ≤ b^2*E := by
  obtain ⟨C,hC,h⟩ := masked_mixed_affine c d 2 hc hcd (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro T R K B D δ r S hT hK hKR hB hBR hD hDR hRT hδ hδ1 hδc hδT hr hr2 hr4 hs hbox
  dsimp only
  let F := squareSmoothing (scaledKernel compactKernel δ) r
  let S₁ := S.image stripAffineIndex
  let S₂ := S.image stripInverseIndex
  have h₁ : ∀ p ∈ S₁, InMixedAffineBox B K R 2 p := by
    intro p hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hbox m hm
    simp only [InMixedAffineBox,stripAffineIndex,Int.cast_neg,abs_neg]
    exact ⟨h1,h2,h3,h4,h6.trans (by linarith)⟩
  have h₂ : ∀ p ∈ S₂, InMixedAffineBox D K R 2 p := by
    intro p hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hbox m hm
    simp only [InMixedAffineBox,stripInverseIndex,Int.cast_neg,abs_neg]
    exact ⟨h5,h6,h3,h4,h2.trans (by linarith)⟩
  have hnonzero (Q : ℝ) (hQ : 1 ≤ Q) (U : Finset (ℤ × (ℤ × ℤ)))
      (hu : ∀ p ∈ U, InMixedAffineBox Q K R 2 p) : ∀ p ∈ U, p.1 ≠ 0 ∧ p.2.1 ≠ 0 := by
    intro p hp
    obtain ⟨h1,h2,h3,h4,h5⟩ := hu p hp
    constructor
    · intro hz; simp only [hz,Int.cast_zero,abs_zero] at h1; linarith
    · intro hz; simp only [hz,Int.cast_zero] at h3; linarith
  obtain ⟨f,hf⟩ := compact_smoothed_general_schwartz hr2 hδ
    (show ∀ x, x ∉ Icc c d → r x^2 = 0 from fun x hx => by rw [hs x hx]; norm_num)
  have hf' : (f : ℝ → ℝ) = F := hf
  have hfm : Measurable F := by rw [← hf']; exact f.continuous.measurable
  have hi₁ : Integrable (fun v => (∑ m ∈ S, F (stripCenter m v))^2) := by
    have hi := (memLp_two_iff_integrable_sq (finite_affine_memLp f S₁ (hnonzero B hB S₁ h₁)).aestronglyMeasurable).mp
      (finite_affine_memLp f S₁ (hnonzero B hB S₁ h₁))
    simpa only [hf',S₁,stripAffine_sum] using hi
  have hi₂ : Integrable (fun v => (∑ m ∈ S, F (-((m.2.2:ℝ)*v+(m.1:ℝ))/(m.2.1:ℝ)))^2) := by
    have hi := (memLp_two_iff_integrable_sq (finite_affine_memLp f S₂ (hnonzero D hD S₂ h₂)).aestronglyMeasurable).mp
      (finite_affine_memLp f S₂ (hnonzero D hD S₂ h₂))
    simpa only [hf',S₂,stripInverse_sum] using hi
  have hb₁ := h T R K B K δ univ r S₁ hT hK hKR hB hBR hK le_rfl hRT
    hδ hδ1 hδc hδT MeasurableSet.univ hr hr2 hr4 hs h₁
  have hb₂ := h T R K D K δ univ r S₂ hT hK hKR hD hDR hK le_rfl hRT
    hδ hδ1 hδc hδT MeasurableSet.univ hr hr2 hr4 hs h₂
  simp only [indicator_univ,Measure.restrict_univ,affineIndexIntegral,S₁,stripAffine_sum] at hb₁
  simp only [indicator_univ,Measure.restrict_univ,affineIndexIntegral,S₂,stripInverse_sum] at hb₂
  obtain ⟨hinv,hinvb⟩ := inverse_ratio_integral hi₂ (fun _ => sq_nonneg _) ha hab
  have hinveq : ∀ᵐ v ∂volume.restrict (Icc a b),
      (∑ m ∈ S, F (-((m.2.2:ℝ)*(1/v)+(m.1:ℝ))/(m.2.1:ℝ)))^2 =
        (∑ m ∈ S, F (stripCenter m v/v))^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    have hm2 : (m.2.1:ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by linarith : 0 < K) (hbox m hm).2.2.1)
    rw [stripCenter,cubic_affine_inversion hm2 (ne_of_gt (ha.trans_le hv.1))]
  refine ⟨hi₁.integrableOn,hinv.congr hinveq,?_,?_⟩
  · exact (setIntegral_le_integral hi₁ (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).trans hb₁
  · exact (integral_congr_ae hinveq).symm.le.trans (hinvb.trans
      (mul_le_mul_of_nonneg_left hb₂ (sq_nonneg b)))

/-- Actual strip-box estimate with all affine energies discharged. Both
numerator signs are allowed; only the denominator is normalized positive.
The designated first mask remains its exact restricted square mass. -/
theorem cubic_mixed_box (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K B D L H : ℝ) (r₀ r : ℝ → ℝ)
      (A₀ : Set ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ K → K ≤ R → 1 ≤ B → B ≤ R → 1 ≤ D → D ≤ R → R ≤ T^4 →
      0 < L → 0 < H →
      max 1 (1/a)*(H/(L*K)) ≤ 1 → max 1 (1/a)*(H/(L*K)) ≤ c/4 →
      (max 1 (1/a)*(H/(L*K)))⁻¹ ≤ T →
      MeasurableSet A₀ → Measurable r₀ → MemLp r₀ 2 → (∀ v, 0 ≤ r₀ v) →
      Measurable r → Integrable (fun x => r x^2) → Integrable (fun x => r x^4) →
      (∀ x, 0 ≤ r x) → (∀ x, x ∉ Icc c d → r x = 0) →
      (∀ m ∈ S, InCubicBox B K D m) →
      IntegrableOn (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) (Icc a b) ∧
      (∫ v in Icc a b, A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) ≤
        C*(H/(L*K))*Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b))*
          Real.sqrt (T^ε*(R^2*K^4*(∫ x, r x^2)^2+R*K^3*(∫ x, r x^4))) := by
  obtain ⟨Ca,hCa,he⟩ := cubic_mixed_energies a b c d ha hab hc hcd hε
  obtain ⟨Ct,hCt,ht⟩ := cubic_strip_integral a b ha hab
  have hb : 0 < b := ha.trans_le hab
  let P := max 1 (b^2)*Ca
  have hP : 0 < P := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCa
  refine ⟨Ct*Real.sqrt b*Real.sqrt P,by positivity,?_⟩
  intro T R K B D L H r₀ r A₀ S hT hK hKR hB hBR hD hDR hRT hL hH hw1 hwc hwT
    hA₀ hr₀ hmem₀ hr₀0 hr hr2 hr4 hr0 hs hbox
  have hKp : 0 < K := by linarith
  have hδ : 0 < H/(L*K) := div_pos hH (mul_pos hL hKp)
  let w := max 1 (1/a)*(H/(L*K))
  have hw : 0 < w := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hδ
  let F := squareSmoothing (scaledKernel compactKernel w) r
  let W := R^2*K^4*(∫ x, r x^2)^2+R*K^3*(∫ x, r x^4)
  have hR0 : 0 ≤ R := (show 0 ≤ K by linarith).trans hKR
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact add_nonneg (by positivity) (mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity)))
  have hTE : 0 ≤ T^ε*W := mul_nonneg (by positivity) hW
  obtain ⟨hiX,hiY,hX,hY⟩ := he T R K B D w r S hT hK hKR hB hBR hD hDR hRT hw hw1 hwc hwT hr hr2 hr4 hs hbox
  obtain ⟨κB,hκB,hκbound⟩ := compactKernel_bound
  obtain ⟨hFm,hFb⟩ := squareSmoothing_bounded_measurable
    (scaledKernel_measurable compactKernel_smooth.continuous.measurable _)
    (scaledKernel_nonneg compactKernel_nonneg hw) (by positivity)
    (scaledKernel_bound hw hκbound) hr hr2
  have hF0 : ∀ x, 0 ≤ F x := fun x => (hFb x).1
  have hFbound : ∀ x, ‖F x‖ ≤ w⁻¹*κB*(∫ y, r y^2) := by
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (hF0 x)]
    exact (hFb x).2
  have hfirst : ∀ m ∈ S, MemLp (fun v => F (stripCenter m v)) 2 (volume.restrict (Icc a b)) := by
    intro m _
    apply MemLp.of_bound (C := w⁻¹*κB*(∫ y, r y^2))
    · exact Filter.Eventually.of_forall (fun v => hFbound _)
    · have hm : Measurable (fun v => F (stripCenter m v)) := by unfold stripCenter; fun_prop
      exact hm.aestronglyMeasurable
  have hsecond : ∀ m ∈ S, MemLp (fun v => F (stripCenter m v/v)) 2 (volume.restrict (Icc a b)) := by
    intro m _
    apply MemLp.of_bound (C := w⁻¹*κB*(∫ y, r y^2))
    · exact Filter.Eventually.of_forall (fun v => hFbound _)
    · have hm : Measurable (fun v => F (stripCenter m v/v)) := by unfold stripCenter; fun_prop
      exact hm.aestronglyMeasurable
  have hcommonX : (∫ v in Icc a b, (∑ m ∈ S, F (stripCenter m v))^2) ≤ P*(T^ε*W) := by
    apply hX.trans
    change Ca*T^ε*W ≤ P*(T^ε*W)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hTE
    exact le_mul_of_one_le_left hCa.le (le_max_left _ _)
  have hcommonY : (∫ v in Icc a b, (∑ m ∈ S, F (stripCenter m v/v))^2) ≤ P*(T^ε*W) := by
    apply hY.trans
    change b^2*(Ca*T^ε*W) ≤ P*(T^ε*W)
    calc
      _ = (b^2*Ca)*(T^ε*W) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hCa.le) hTE
  have hmasked := masked_box_of_energy_bounds (μ := volume.restrict (Icc a b)) S hA₀
    (hmem₀.restrict _) hfirst hsecond hr₀0 (fun _ v => hF0 _) (fun _ v => hF0 _)
    (mul_nonneg hP.le hTE) hcommonX hcommonY
  have hstrip := ht L H K S A₀ r₀ r hL hH hKp (fun m hm => (hbox m hm).2.2.1)
    hA₀ hr₀ hmem₀ hr₀0 hr hr2 hr0
  refine ⟨hstrip.1,?_⟩
  have hmasked' : (∫ v in Icc a b, A₀.indicator r₀ v * ∑ m ∈ S, smoothedStripPair r a (H/(L*K)) m v) ≤
      Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b))*Real.sqrt (P*(T^ε*W)) := hmasked
  calc
    _ ≤ (Ct*(H/(L*K))*Real.sqrt b)*
      (Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b))*Real.sqrt (P*(T^ε*W))) :=
        hstrip.2.2.trans (mul_le_mul_of_nonneg_left hmasked' (by positivity))
    _ = _ := by rw [Real.sqrt_mul hP.le]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.stripAffineIndex_injective
#print axioms GuthMaynard.Improvement.stripInverseIndex_injective
#print axioms GuthMaynard.Improvement.stripAffine_sum
#print axioms GuthMaynard.Improvement.stripInverse_sum
#print axioms GuthMaynard.Improvement.finite_affine_memLp
#print axioms GuthMaynard.Improvement.cubic_mixed_energies
#print axioms GuthMaynard.Improvement.cubic_mixed_box
