module
public import GuthMaynard.Improvement.ShortPoweredDetectorFamily
public import GuthMaynard.Improvement.ShortWindowLargeValues
public import GuthMaynard.Improvement.RealIntegerSource
public import MathCollab.Density.ZeroSeparation

@[expose] public section

open Complex Filter Set MathCollab.Density
open scoped Topology BigOperators
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
namespace GuthMaynard.Improvement

/-- Actual Type-I detection of an ordinate-injective separated finite family.
The constant and height threshold precede sigma, translation and the family. -/
theorem short_typeI_separated_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ t₀ : ℝ) (R : Finset ℂ),
      9/13 ≤ σ → σ ≤ 5/7 →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ.im ∈ Icc t₀ (t₀+H) ∧
        (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(shortDensityExponent σ+ε) := by
  classical
  let η : ℝ := min (ε/100) (1/100)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ 1/100 := min_le_right _ _
  have hηeps : η ≤ ε/100 := min_le_left _ _
  obtain ⟨C,hC,hLV⟩ := short_window_large_values hη hηsmall
  have hloglim := (isLittleO_log_rpow_rpow_atTop (2:ℝ) hη).tendsto_div_nhds_zero
  norm_num at hloglim
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ), shortPoweredDetectorFamily_cover hη,
    shortPoweredDetectorFamily_coefficients hη,
    (tendsto_rpow_atTop hη).eventually_ge_atTop ((2:ℝ)^99),
    (tendsto_rpow_atTop (show (0:ℝ)<3/4 by norm_num)).eventually_ge_atTop 2,
    hloglim.eventually (gt_mem_nhds (show (0:ℝ)<1/600000 by norm_num))]
    with H hH hfamily hcoeff hconst hlength hlog
  intro σ t₀ R hσ hσ' hcard hsep hR
  have hHpos : 0 < H := by linarith
  have hHa : 1 ≤ H := by linarith
  have hsc := short_density_scale_bounds hσ hσ'
  let J := (shortPoweredDetectorIndices H).filter (fun p =>
    H^(shortDensityA σ) ≤ (shortPoweredDetectorScale p:ℝ) ∧
    (shortPoweredDetectorScale p:ℝ) ≤ (2:ℝ)^99*H^(shortDensityB σ) ∧
    2*(shortPoweredDetectorScale p:ℝ) ≤ H^2)
  let W := R.image Complex.im
  let Wj := fun p => W.filter (fun t =>
    (shortPoweredDetectorScale p:ℝ)^σ*H^(-2*η) ≤
      ‖detectingPolynomial (shortPoweredDetectorScale p) (shortPoweredDetectorFamilyCoeff η H p) t‖)
  have hWj : ∀ p ∈ J, ((Wj p).card:ℝ) ≤ C*H^(shortDensityExponent σ+10*η) := by
    intro p hp
    obtain ⟨hp,hlow,hhigh,hsupport⟩ := Finset.mem_filter.mp hp
    have hN : 2 ≤ (shortPoweredDetectorScale p:ℝ) :=
      hlength.trans ((Real.rpow_le_rpow_of_exponent_le hHa hsc.1).trans hlow)
    have hupper : (shortPoweredDetectorScale p:ℝ) ≤ H^(shortDensityB σ+η) := by
      calc
        _ ≤ (2:ℝ)^99*H^(shortDensityB σ) := hhigh
        _ ≤ H^η*H^(shortDensityB σ) := mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = _ := by rw [← Real.rpow_add hHpos]; congr 1; ring
    have hc : ∀ n ∈ sourceRatioIndices (shortPoweredDetectorScale p:ℝ),
        ‖shortPoweredDetectorFamilyCoeff η H p n‖ ≤ 1 := by
      intro n hn
      apply hcoeff p hp hsupport n
      simpa only [sourceRatioIndices, show 2*(shortPoweredDetectorScale p:ℝ) =
        ((2*shortPoweredDetectorScale p:ℕ):ℝ) by push_cast; rfl, Nat.floor_natCast] using hn
    apply hLV σ H (shortPoweredDetectorScale p:ℝ) t₀
      (shortPoweredDetectorFamilyCoeff η H p) (Wj p) hσ hσ' hH hN hlow hupper hc
    · intro t ht
      obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
      exact (hR ρ hρ).2.2.1
    · intro t ht s hs hne
      exact hsep t (Finset.mem_filter.mp ht).1 s (Finset.mem_filter.mp hs).1 hne
    · intro t ht
      simpa only [← detectingPolynomial_eq_boundedPolynomial] using (Finset.mem_filter.mp ht).2
  have hcover : W ⊆ J.biUnion Wj := by
    intro t ht
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hβ,hβ',_hloc,hd⟩ := hR ρ hρ
    obtain ⟨p,hp,hlo,hhi,hsupport,hlarge⟩ := hfamily.2 (shortDensityA σ) σ ρ
      hsc.1 hsc.2.1 (by linarith) hβ hβ' hd
    apply Finset.mem_biUnion.mpr
    refine ⟨p,Finset.mem_filter.mpr ⟨hp,hlo,hhi,hsupport⟩,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨ρ,hρ,rfl⟩,hlarge⟩
  have hJ : (J.card:ℝ) ≤ H^η := by
    have hsmall : 600000*(Real.log H)^2 ≤ H^η := by
      have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hHpos η)).mp hlog
      linarith
    exact (show (J.card:ℝ) ≤ (shortPoweredDetectorIndices H).card by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)).trans (hfamily.1.trans hsmall)
  have hsum : (W.card:ℝ) ≤ (J.card:ℝ)*(C*H^(shortDensityExponent σ+10*η)) := by
    calc
      _ ≤ ∑ p ∈ J, ((Wj p).card:ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ J, C*H^(shortDensityExponent σ+10*η) := Finset.sum_le_sum hWj
      _ = _ := by simp
  have hpow : H^(shortDensityExponent σ+11*η) ≤ H^(shortDensityExponent σ+ε) :=
    Real.rpow_le_rpow_of_exponent_le hHa (by linarith)
  calc
    _ = (W.card:ℝ) := by rw [hcard]
    _ ≤ (J.card:ℝ)*(C*H^(shortDensityExponent σ+10*η)) := hsum
    _ ≤ H^η*(C*H^(shortDensityExponent σ+10*η)) :=
      mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = C*H^(shortDensityExponent σ+11*η) := by
      rw [← mul_left_comm, ← Real.rpow_add hHpos]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hC.le

/-- The Type-I branch count on actual zero-slab representatives. -/
theorem short_typeI_zero_slab_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ : ℝ) (R : Finset ℂ),
      9/13 ≤ σ → σ ≤ 5/7 → R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(shortDensityExponent σ+ε) := by
  obtain ⟨C,hC,hcount⟩ := short_typeI_separated_count hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with H hh
  intro σ R hσ hσ' hR hcard hsep hlarge
  apply hh σ H R hσ hσ' hcard hsep
  intro ρ hρ
  obtain ⟨hz,hβ,hγ,hγ'⟩ := mem_zetaZeroFinset.mp (hR hρ)
  exact ⟨hβ,hz.2.2.le,⟨hγ,by linarith⟩,hlarge ρ hρ⟩

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_typeI_separated_count

#print axioms GuthMaynard.Improvement.short_typeI_zero_slab_count
