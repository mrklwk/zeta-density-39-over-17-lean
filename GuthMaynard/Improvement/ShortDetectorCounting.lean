module
public import GuthMaynard.Improvement.ShortLocalZeroCount
public import GuthMaynard.Improvement.ShortDetectorAlternative

@[expose] public section

open Complex Filter Set MathCollab.Density
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The actual detector alternatives restore all zero multiplicities once
their separated finite counts are bounded. Both branch bounds remain explicit;
this theorem does not postulate either analytic estimate. The constant and
height threshold precede sigma and both candidate bounds. -/
theorem short_slab_count_of_separated_branch_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ σ BI BII : ℝ,
      9/13 ≤ σ →
      (∀ R : Finset ℂ, R ⊆ zetaZeroFinset σ H (2*H) →
        (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
        (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) → (R.card:ℝ) ≤ BI) →
      (∀ R : Finset ℂ, R ⊆ zetaZeroFinset σ H (2*H) →
        (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
        (∀ ρ ∈ R, (1/3:ℝ) ≤
          ‖detectorIntegral ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))‖) →
        (R.card:ℝ) ≤ BII) →
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*Real.log (2*H)*(BI+BII) := by
  classical
  obtain ⟨C,hC,hrestore⟩ := short_zeta_separated_representatives
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ), short_detector_eventually_alternative]
    with H hH halt
  intro σ BI BII hσ hI hII
  obtain ⟨R,hR,hcard,hsep,hcount⟩ := hrestore σ H hσ hH
  let P := fun ρ : ℂ => (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖
  let RI := R.filter P
  let RII := R.filter (fun ρ => ¬ P ρ)
  have hRI : RI ⊆ R := Finset.filter_subset _ _
  have hRII : RII ⊆ R := Finset.filter_subset _ _
  have hinj : Set.InjOn Complex.im (R:Set ℂ) := Finset.injOn_of_card_image_eq hcard
  have hIc : (RI.image Complex.im).card = RI.card :=
    Finset.card_image_of_injOn (hinj.mono hRI)
  have hIIc : (RII.image Complex.im).card = RII.card :=
    Finset.card_image_of_injOn (hinj.mono hRII)
  have hIs : oneSeparated (RI.image Complex.im) :=
    oneSeparated_subset hsep (Finset.image_subset_image hRI)
  have hIIs : oneSeparated (RII.image Complex.im) :=
    oneSeparated_subset hsep (Finset.image_subset_image hRII)
  have hbI := hI RI (hRI.trans hR) hIc hIs (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  have hbII := hII RII (hRII.trans hR) hIIc hIIs (by
    intro ρ hρ
    obtain ⟨hz,hβ,hγ,hγ'⟩ := mem_zetaZeroFinset.mp (hR (hRII hρ))
    have habs : |ρ.im| = ρ.im := abs_of_nonneg (by linarith)
    rcases halt ρ (hσ.trans hβ) hz.2.2 (by rwa [habs]) (by rwa [habs]) hz.1
      with hi | hii
    · exact ((Finset.mem_filter.mp hρ).2 hi).elim
    · exact hii)
  have hc : RI.card+RII.card = R.card := Finset.card_filter_add_card_filter_not _
  have hsum : (R.card:ℝ) ≤ BI+BII := by
    have hcast : (RI.card:ℝ)+(RII.card:ℝ) = (R.card:ℝ) := by exact_mod_cast hc
    linarith
  exact hcount.trans (mul_le_mul_of_nonneg_left hsum
    (mul_nonneg hC.le (Real.log_nonneg (by linarith))))

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_slab_count_of_separated_branch_bounds
