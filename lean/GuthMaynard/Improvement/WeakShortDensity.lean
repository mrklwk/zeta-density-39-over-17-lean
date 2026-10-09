import GuthMaynard.Improvement.ShortTypeICount
import GuthMaynard.Improvement.WeakTypeIICount
import GuthMaynard.Improvement.ShortDetectorCounting
import MathCollab.Density.DensityDyadicSummation

open Complex Filter Set MathCollab.Density
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Actual Type-II zero representatives from the ordinary fourth moment. -/
theorem weak_short_typeII_zero_slab_count
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ : ℝ) (R : Finset ℂ),
      9/13 ≤ σ → R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤
        ‖detectorIntegral ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))‖) →
      (R.card:ℝ) ≤ C*H^(2-2*σ+1/25+ε) := by
  classical
  obtain ⟨C,H₀,hC,_hH₀,hcount⟩ := weak_short_typeII_count hε
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

/-- The Type-II exponent fits the target throughout the closed sigma window. -/
theorem weak_short_typeII_exponent_le {σ : ℝ} (hσ : 9/13 ≤ σ) (hσ' : σ ≤ 5/7) :
    2-2*σ+1/25 ≤ shortDensityExponent σ := by
  have hd : 0 < 7*σ+3 := by linarith
  rw [shortDensityExponent,le_div_iff₀ hd]
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (show 7*σ-5 ≤ 0 by linarith)
    (show 28*σ-33 ≤ 0 by linarith)]

/-- Uniform actual slab density using the weaker, proved moment estimate.
Both separated branch estimates, contour detection and analytic multiplicity
restoration are proved dependencies. -/
theorem short_slab_density
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ σ : ℝ,
      9/13 ≤ σ → σ ≤ 5/7 →
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*H^(shortDensityExponent σ+ε) := by
  have hη : 0 < ε/2 := by positivity
  obtain ⟨CI,hCI,hI⟩ := short_typeI_zero_slab_count hη
  obtain ⟨CII,hCII,hII⟩ := weak_short_typeII_zero_slab_count hη
  obtain ⟨C₀,hC₀,hrestore⟩ := short_slab_count_of_separated_branch_bounds
  let D : ℝ := Real.log 2+1/(ε/2)
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hη)
  refine ⟨C₀*(CI+CII)*D,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),hI,hII,hrestore] with H hH hi hii hr
  intro σ hσ hσ'
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hb := hr σ (CI*H^(shortDensityExponent σ+ε/2))
    (CII*H^(shortDensityExponent σ+ε/2)) hσ (fun R hR hc hs hl => hi σ R hσ hσ' hR hc hs hl) (by
      intro R hR hc hs hl
      exact (hii σ R hσ hR hc hs hl).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH1
          (by linarith [weak_short_typeII_exponent_le hσ hσ'])) hCII.le))
  have hlog : Real.log (2*H) ≤ D*H^(ε/2) := classical_log_budget hH1 hη
  calc
    _ ≤ C₀*Real.log (2*H)*(CI*H^(shortDensityExponent σ+ε/2)+CII*H^(shortDensityExponent σ+ε/2)) := hb
    _ ≤ C₀*(D*H^(ε/2))*(CI*H^(shortDensityExponent σ+ε/2)+CII*H^(shortDensityExponent σ+ε/2)) := by gcongr
    _ = (C₀*(CI+CII)*D)*(H^(ε/2)*H^(shortDensityExponent σ+ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring

/-- All actual zeros with analytic multiplicity and both signs. The audited
fixed-sigma dyadic summation is reused, so this constant may depend on sigma. -/
theorem short_density
    {σ ε : ℝ} (hσ : 9/13 ≤ σ) (hσ' : σ ≤ 5/7) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(18*(1-σ)/(7*σ+3)+ε) := by
  obtain ⟨C,hC,hslab⟩ := short_slab_density hε
  have hp : 0 < shortDensityExponent σ+ε := by
    have he := (short_density_scale_bounds hσ hσ').2.2.2.2.1
    linarith
  apply zetaDensity_bound_of_eventual_slabs hp hC
  filter_upwards [hslab] with H hh
  exact hh σ hσ hσ'

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.weak_short_typeII_zero_slab_count
#print axioms GuthMaynard.Improvement.weak_short_typeII_exponent_le
#print axioms GuthMaynard.Improvement.short_slab_density
#print axioms GuthMaynard.Improvement.short_density
