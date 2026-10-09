import GuthMaynard.Improvement.CubicMixedBox
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

def negateCubicMode (m : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) := (-m.1,-m.2.1,-m.2.2)
def InSignedCubicBox (B K D : ℝ) (m : ℤ × (ℤ × ℤ)) : Prop :=
  B ≤ |(m.1:ℝ)| ∧ |(m.1:ℝ)| ≤ 2*B ∧ K ≤ |(m.2.1:ℝ)| ∧
    |(m.2.1:ℝ)| ≤ 2*K ∧ D ≤ |(m.2.2:ℝ)| ∧ |(m.2.2:ℝ)| ≤ 2*D

theorem negateCubicMode_involutive : Function.Involutive negateCubicMode := by
  intro m
  simp [negateCubicMode]

theorem negateCubicMode_injective : Function.Injective negateCubicMode :=
  negateCubicMode_involutive.injective

theorem stripCenter_negate (m : ℤ × (ℤ × ℤ)) (v : ℝ) :
    stripCenter (negateCubicMode m) v = stripCenter m v := by
  unfold stripCenter negateCubicMode
  push_cast
  rw [show -(-(m.1:ℝ)*v+ -(m.2.2:ℝ)) = -(-((m.1:ℝ)*v+(m.2.2:ℝ))) by ring,neg_div_neg_eq]

theorem cubicStripMass_negate (r : ℝ → ℝ) (L H : ℝ) (m : ℤ × (ℤ × ℤ)) (v : ℝ) :
    cubicStripMass r L H (negateCubicMode m) v = cubicStripMass r L H m v := by
  unfold cubicStripMass negateCubicMode
  have hlin (y : ℝ) : L*(((-m.1:ℤ):ℝ)*v+((-m.2.1:ℤ):ℝ)*y+((-m.2.2:ℤ):ℝ)) =
      -(L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))) := by push_cast; ring
  simp only [hlin,abs_neg]

theorem smoothedStripPair_negate (r : ℝ → ℝ) (a δ : ℝ) (m : ℤ × (ℤ × ℤ)) (v : ℝ) :
    smoothedStripPair r a δ (negateCubicMode m) v = smoothedStripPair r a δ m v := by
  simp only [smoothedStripPair,stripCenter_negate]

theorem cubicStripMass_sum_negate (S : Finset (ℤ × (ℤ × ℤ))) (r : ℝ → ℝ) (L H v : ℝ) :
    (∑ m ∈ S.image negateCubicMode, cubicStripMass r L H m v) =
      ∑ m ∈ S, cubicStripMass r L H m v := by
  rw [Finset.sum_image (fun _ _ _ _ h => negateCubicMode_injective h)]
  simp only [cubicStripMass_negate]

/-- Literal first mask and outer integral are unchanged by mode negation. -/
theorem cubicStripIntegral_negate (S : Finset (ℤ × (ℤ × ℤ))) (r₀ r : ℝ → ℝ)
    (A₀ V : Set ℝ) (L H : ℝ) :
    (∫ v in V, A₀.indicator r₀ v * ∑ m ∈ S.image negateCubicMode, cubicStripMass r L H m v) =
      ∫ v in V, A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v := by
  simp only [cubicStripMass_sum_negate]

theorem signed_box_positive {B K D : ℝ} {m : ℤ × (ℤ × ℤ)}
    (hbox : InSignedCubicBox B K D m) (hm : 0 < m.2.1) : InCubicBox B K D m := by
  have hm' : (0:ℝ) < (m.2.1:ℝ) := by exact_mod_cast hm
  simpa only [InSignedCubicBox,InCubicBox,abs_of_pos hm'] using hbox

theorem signed_box_negative {B K D : ℝ} {m : ℤ × (ℤ × ℤ)}
    (hbox : InSignedCubicBox B K D m) (hm : m.2.1 < 0) : InCubicBox B K D (negateCubicMode m) := by
  have hm' : (m.2.1:ℝ) < 0 := by exact_mod_cast hm
  simpa only [InSignedCubicBox,InCubicBox,negateCubicMode,Int.cast_neg,abs_neg,abs_of_neg hm'] using hbox

/-- Two sign pieces, counted separately even when normalized images overlap.
There is no injectivity claim across the union of the two pieces. -/
theorem cubicStripMass_sign_split (S : Finset (ℤ × (ℤ × ℤ)))
    (hS : ∀ m ∈ S, m.2.1 ≠ 0) (r : ℝ → ℝ) (L H v : ℝ) :
    (∑ m ∈ S, cubicStripMass r L H m v) =
      (∑ m ∈ S.filter (fun m => 0 < m.2.1), cubicStripMass r L H m v) +
      ∑ m ∈ (S.filter (fun m => m.2.1 < 0)).image negateCubicMode, cubicStripMass r L H m v := by
  rw [cubicStripMass_sum_negate]
  have hfilters : S.filter (fun m => ¬ 0 < m.2.1) = S.filter (fun m => m.2.1 < 0) := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · intro hm; exact ⟨hm.1,lt_of_le_of_ne (le_of_not_gt hm.2) (hS m hm.1)⟩
    · intro hm; exact ⟨hm.1,not_lt_of_ge hm.2.le⟩
  simpa only [hfilters] using
    (Finset.sum_filter_add_sum_filter_not S (fun m => 0 < m.2.1) (fun m => cubicStripMass r L H m v)).symm

/-- Actual mixed strip-box bound for arbitrary signs in all three modes.
Exactly two denominator-sign pieces account for the factor two in the
constant; the designated Fourier mask remains unchanged. -/
theorem signed_cubic_mixed_box (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b)
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
      (∀ m ∈ S, InSignedCubicBox B K D m) →
      IntegrableOn (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) (Icc a b) ∧
      (∫ v in Icc a b, A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) ≤
        C*(H/(L*K))*Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b))*
          Real.sqrt (T^ε*(R^2*K^4*(∫ x, r x^2)^2+R*K^3*(∫ x, r x^4))) := by
  obtain ⟨C,hC,h⟩ := cubic_mixed_box a b c d ha hab hc hcd hε
  refine ⟨2*C,by positivity,?_⟩
  intro T R K B D L H r₀ r A₀ S hT hK hKR hB hBR hD hDR hRT hL hH hw1 hwc hwT
    hA₀ hr₀ hmem₀ hr₀0 hr hr2 hr4 hr0 hs hbox
  let P := S.filter (fun m => 0 < m.2.1)
  let N := (S.filter (fun m => m.2.1 < 0)).image negateCubicMode
  have hP : ∀ m ∈ P, InCubicBox B K D m := by
    intro m hm
    obtain ⟨hmS,hm0⟩ := Finset.mem_filter.mp hm
    exact signed_box_positive (hbox m hmS) hm0
  have hN : ∀ m ∈ N, InCubicBox B K D m := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hnS,hn0⟩ := Finset.mem_filter.mp hn
    exact signed_box_negative (hbox n hnS) hn0
  have hnonzero : ∀ m ∈ S, m.2.1 ≠ 0 := by
    intro m hm hz
    have hh := (hbox m hm).2.2.1
    rw [hz,Int.cast_zero,abs_zero] at hh
    linarith
  obtain ⟨hiP,hbP⟩ := h T R K B D L H r₀ r A₀ P hT hK hKR hB hBR hD hDR hRT
    hL hH hw1 hwc hwT hA₀ hr₀ hmem₀ hr₀0 hr hr2 hr4 hr0 hs hP
  obtain ⟨hiN,hbN⟩ := h T R K B D L H r₀ r A₀ N hT hK hKR hB hBR hD hDR hRT
    hL hH hw1 hwc hwT hA₀ hr₀ hmem₀ hr₀0 hr hr2 hr4 hr0 hs hN
  have heq : (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) =
      (fun v => A₀.indicator r₀ v * ∑ m ∈ P, cubicStripMass r L H m v) +
      (fun v => A₀.indicator r₀ v * ∑ m ∈ N, cubicStripMass r L H m v) := by
    funext v
    rw [cubicStripMass_sign_split S hnonzero r L H v,mul_add]
    rfl
  refine ⟨by rw [heq]; exact hiP.add hiN,?_⟩
  rw [heq]
  simp only [Pi.add_def]
  rw [integral_add hiP hiN]
  nlinarith only [hbP,hbN]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.negateCubicMode_involutive
#print axioms GuthMaynard.Improvement.negateCubicMode_injective
#print axioms GuthMaynard.Improvement.stripCenter_negate
#print axioms GuthMaynard.Improvement.cubicStripMass_negate
#print axioms GuthMaynard.Improvement.smoothedStripPair_negate
#print axioms GuthMaynard.Improvement.cubicStripMass_sum_negate
#print axioms GuthMaynard.Improvement.cubicStripIntegral_negate
#print axioms GuthMaynard.Improvement.signed_box_positive
#print axioms GuthMaynard.Improvement.signed_box_negative
#print axioms GuthMaynard.Improvement.cubicStripMass_sign_split
#print axioms GuthMaynard.Improvement.signed_cubic_mixed_box
