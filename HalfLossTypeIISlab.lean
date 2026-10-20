module
public import GuthMaynard.Improvement.ShortTypeICount
public import HalfLossTypeIICount
public import GuthMaynard.Improvement.ShortDetectorCounting
public import MathCollab.Density.DensityDyadicSummation

@[expose] public section

open Complex Filter Set MathCollab.Density
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Actual Type-II zero representatives from the ordinary fourth moment. -/
theorem half_loss_typeII_zero_slab_count
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ : ℝ) (R : Finset ℂ),
      9/13 ≤ σ → R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤
        ‖detectorIntegral ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))‖) →
      (R.card:ℝ) ≤ C*H^(2-2*σ+1/50+ε) := by
  classical
  obtain ⟨C,H₀,hC,_hH₀,hcount⟩ := half_loss_short_typeII_count hε
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop H₀] with H hH
  intro σ R hσ hR hcard hsep hlarge
  let W := R.image Complex.im
  have hex : ∀ u : ℝ, ∃ ρ : ℂ, u ∈ W → ρ ∈ R ∧ ρ.im=u := by
    intro u
    by_cases hu : u ∈ W
    · obtain ⟨ρ,hρ,he⟩ := Finset.mem_image.mp hu
      exact ⟨ρ,fun _ => ⟨hρ,he⟩⟩
    · exact ⟨0,fun hh => (hu hh).elim⟩
  choose ρ hρ using hex
  have hc := hcount H hH σ W ρ hσ hsep (by
    intro u hu
    obtain ⟨hr,he⟩ := hρ u hu
    obtain ⟨_hz,_hβ,hlo,hhi⟩ := mem_zetaZeroFinset.mp (hR hr)
    simpa only [mem_Icc,he] using And.intro hlo hhi) (by
    intro u hu
    obtain ⟨hr,he⟩ := hρ u hu
    obtain ⟨hz,hβ,_hlo,_hhi⟩ := mem_zetaZeroFinset.mp (hR hr)
    exact ⟨he,hβ,hz.2.2.le⟩) (by
    intro u hu
    simpa only [one_div] using hlarge (ρ u) (hρ u hu).1)
  simpa only [W,hcard] using hc


end GuthMaynard.Improvement
