module
public import GuthMaynard.Improvement.ShortDetectorWindowDetection
public import GuthMaynard.Improvement.ShortTypeIIPacking

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- Actual separated TypeII count reduced to the actual fourth moment, with
no tail, Holder, or packing premise. Representatives may have different beta. -/
theorem short_typeII_count_by_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ σ : ℝ,
      ∀ (W : Finset ℝ) (ρ : ℝ → ℂ), 9/13 ≤ σ →
      oneSeparated W → (∀ u ∈ W,u ∈ Icc H (2*H)) →
      (∀ u ∈ W,(ρ u).im=u ∧ σ ≤ (ρ u).re ∧ (ρ u).re ≤ 1) →
      (∀ u ∈ W,(1/3:ℝ) ≤ ‖detectorIntegral (ρ u) (2*H^((1:ℝ)/100)) (H^((1:ℝ)/2))‖) →
      (W.card:ℝ) ≤ C*H^(1-2*σ)*(∫ t in Icc (H/2) (3*H),(shortTwistedNorm H t)^4) := by
  obtain ⟨A,hA,hdet⟩ := short_detector_window_fourth
  obtain ⟨B,hB,hpack⟩ := short_typeII_window_packing
  refine ⟨A*B,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),hdet] with H hH hd
  intro σ W ρ hσ hsep hw hρ hlarge
  let J := fun u : ℝ => ∫ v in Icc (-(H/2)) (H/2),
    ‖Complex.Gamma (((1/2-(ρ u).re:ℝ):ℂ)+(v:ℂ)*I)‖*(shortTwistedNorm H (u+v))^4
  have hone (u : ℝ) (hu : u ∈ W) : (1:ℝ) ≤ A*H^(1-2*σ)*J u := by
    obtain ⟨him,hlo,hhi⟩ := hρ u hu
    have hγ : |(ρ u).im| ≤ 2*H := by
      rw [him,abs_of_nonneg (show 0 ≤ u by linarith [(hw u hu).1])]
      exact (hw u hu).2
    have hh := hd σ (ρ u) hσ hlo hhi hγ (hlarge u hu)
    simpa only [him] using hh
  have hs : (W.card:ℝ) ≤ A*H^(1-2*σ)*(∑ u ∈ W,J u) := by
    have hh := Finset.sum_le_sum hone
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,← Finset.mul_sum] using hh
  have hp := hpack H (by linarith) W ρ hsep hw (fun u hu => ⟨hσ.trans (hρ u hu).2.1,(hρ u hu).2.2⟩)
  calc
    _ ≤ A*H^(1-2*σ)*(B*(∫ t in Icc (H/2) (3*H),(shortTwistedNorm H t)^4)) :=
      hs.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = _ := by ring

/-- Conditional only on the explicitly named actual short Mobius fourth
moment. All contour detection, ordinate truncation and separated counting
steps are proved. The constants precede sigma, height and every finite family. -/
theorem short_typeII_count_of_fourth_moment (hmoment : ShortMobiusFourthMoment)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C H₀ : ℝ, 0 < C ∧ 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ σ : ℝ,
      ∀ (W : Finset ℝ) (ρ : ℝ → ℂ), 9/13 ≤ σ →
      oneSeparated W → (∀ u ∈ W,u ∈ Icc H (2*H)) →
      (∀ u ∈ W,(ρ u).im=u ∧ σ ≤ (ρ u).re ∧ (ρ u).re ≤ 1) →
      (∀ u ∈ W,(1/3:ℝ) ≤ ‖detectorIntegral (ρ u) (2*H^((1:ℝ)/100)) (H^((1:ℝ)/2))‖) →
      (W.card:ℝ) ≤ C*H^(2-2*σ+ε) := by
  obtain ⟨A,hA,ha⟩ := short_typeII_count_by_moment
  obtain ⟨H₁,hH₁⟩ := eventually_atTop.mp ha
  obtain ⟨B,H₂,hB,hH₂,hb⟩ := hmoment ε hε
  refine ⟨A*B,max 2 (max H₁ H₂),by positivity,le_max_left _ _,?_⟩
  intro H hH σ W ρ hσ hsep hw hρ hlarge
  have hH1 : H₁ ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hH2 : H₂ ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hn : 0 < H := by linarith [hH₂]
  have hc := hH₁ H hH1 σ W ρ hσ hsep hw hρ hlarge
  have hm := hb H hH2
  change (∫ t in Icc (H/2) (3*H),(shortTwistedNorm H t)^4) ≤ B*H^(1+ε) at hm
  calc
    _ ≤ A*H^(1-2*σ)*(B*H^(1+ε)) := hc.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = (A*B)*(H^(1-2*σ)*H^(1+ε)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_typeII_count_by_moment
#print axioms GuthMaynard.Improvement.short_typeII_count_of_fourth_moment
