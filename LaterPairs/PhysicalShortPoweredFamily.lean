module
public import LaterPairs.PhysicalShortTaylorCover
public import RetunedShortPoweredFamily
public import RetunedShortTaylorCover
public import MathCollab.Density.Stronger.ShortPoweredHeight

@[expose] public section

open Real Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger
open MathCollab.Density

/- This bound is fixed by sigma and delta, before T and any zero. -/
/- The complete finite powered family, restricted by scale conditions that
are independent of the zero. The original smooth scale remains in q.1.1. -/
theorem smoothPoweredFamilyScale_pos (q : (ℤ × ℕ × ℕ) × ℕ × ℕ) :
    0 < smoothPoweredFamilyScale q := by
  unfold smoothPoweredFamilyScale
  exact mul_pos (by positivity) (pow_pos (smoothHalfScale_pos _ _) _)

theorem mem_smoothPoweredIndices {a δ T : ℝ} {q : (ℤ × ℕ × ℕ) × ℕ × ℕ} :
    q ∈ smoothPoweredIndices a δ T ↔
      q.1 ∈ smoothTaylorIndices a T ∧
      1 ≤ q.2.1 ∧ q.2.1 ≤ smoothPowerBound a δ ∧ q.2.2 < q.2.1 ∧
      T^(a) ≤ (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ∧
      (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ≤ T^(smoothingExponent a) := by
  constructor
  · intro hq
    obtain ⟨hbase, hlt, hlo, hhi⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp, hkl⟩ := Finset.mem_product.mp hbase
    obtain ⟨hk, hl⟩ := Finset.mem_product.mp hkl
    have hk' := Finset.mem_Icc.mp hk
    exact ⟨hp, hk'.1, hk'.2, hlt, hlo, hhi⟩
  · rintro ⟨hp, hk0, hkK, hl, hlo, hhi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hp, Finset.mem_product.mpr ?_⟩, hl, hlo, hhi⟩
    exact ⟨Finset.mem_Icc.mpr ⟨hk0, hkK⟩, Finset.mem_range.mpr (lt_of_lt_of_le hl hkK)⟩

theorem smoothTaylorIndices_card_eventually {σ a : ℝ} (hw : PhysicalDetectorWindow σ a) :
    ∀ᶠ T : ℝ in atTop, ((smoothTaylorIndices a T).card : ℝ) ≤ 144*(Real.log T)^2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    log_sq_eventually_le_height] with T hT hlog hsq
  have hYlo : 1 ≤ detectorY a T := Real.one_le_rpow hT (smoothingExponent_pos_physical hw).le
  have hYhi : detectorY a T ≤ T := by
    simpa only [detectorY, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (smoothingExponent_lt_one_physical hw).le
  have hR : 1 ≤ detectorY a T*(Real.log T)^2 := by nlinarith
  have hRhi : detectorY a T*(Real.log T)^2 ≤ T^2 := by nlinarith
  exact smoothTaylorIndices_card_le_log (smoothScaleIndices_card_le_log hT hlog hR hRhi) hlog

/- At most a fixed multiple of log(T)^2 members, before zeros are selected. -/
theorem smoothPoweredIndices_card_eventually {σ a : ℝ} (hw : PhysicalDetectorWindow σ a) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ((smoothPoweredIndices a δ T).card : ℝ) ≤
        144*(smoothPowerBound a δ : ℝ)^2*(Real.log T)^2 := by
  filter_upwards [smoothTaylorIndices_card_eventually hw] with T hcard
  have hh := Finset.card_le_card (Finset.filter_subset
    (fun q : (ℤ × ℕ × ℕ) × ℕ × ℕ => q.2.2 < q.2.1 ∧
      T^(a) ≤ (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ∧
      (smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 ≤ T^(smoothingExponent a))
    ((smoothTaylorIndices a T).product
      ((Finset.Icc 1 (smoothPowerBound a δ)).product (Finset.range (smoothPowerBound a δ)))))
  have hc : ((smoothPoweredIndices a δ T).card : ℝ) ≤
      ((smoothTaylorIndices a T).card : ℝ)*(smoothPowerBound a δ : ℝ)^2 := by
    exact_mod_cast (by simpa [smoothPoweredIndices, Nat.card_Icc, pow_two] using hh)
  calc
    _ ≤ ((smoothTaylorIndices a T).card : ℝ)*(smoothPowerBound a δ : ℝ)^2 := hc
    _ ≤ (144*(Real.log T)^2)*(smoothPowerBound a δ : ℝ)^2 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/- Every member of the fixed family has the required powered scales and
globally bounded normalized coefficients. Threshold precedes every index. -/
theorem smoothPoweredFamily_admissible {σ a η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hη : 0 < η) (δ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ q ∈ smoothPoweredIndices a δ T,
      T^(a) ≤ (smoothPoweredFamilyScale q : ℝ) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ (2 : ℝ)^(smoothPowerBound a δ)*T^(smoothingExponent a) ∧
      (smoothPoweredFamilyScale q : ℝ) ≤ T ∧
      ∀ n : ℕ, ‖smoothPoweredFamilyCoefficient η a δ T q n‖ ≤ 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    fixed_scale_factor_eventually_below_height (C := (2 : ℝ)^(smoothPowerBound a δ)) (smoothingExponent_lt_one_physical hw),
    normalizedSmoothPoweredCoefficient_eventually hη (smoothPowerBound a δ)] with T hT hupper hnorm
  intro q hq
  obtain ⟨_, _, hkK, hl, hlo, hhi⟩ := mem_smoothPoweredIndices.mp hq
  have hs := bounded_power_piece_scales (Nat.cast_nonneg (smoothHalfScale q.1.1 q.1.2.1)) hkK hl hlo hhi
  have he : (smoothPoweredFamilyScale q : ℝ) =
      (2 : ℝ)^q.2.2*(smoothHalfScale q.1.1 q.1.2.1 : ℝ)^q.2.1 := by
    simp [smoothPoweredFamilyScale]
  refine ⟨by rw [he]; exact hs.1, by rw [he]; exact hs.2, ?_, ?_⟩
  · rw [he]
    exact hs.2.trans hupper
  · have hsupp := bounded_power_support_scale
      (Nat.cast_nonneg (smoothHalfScale q.1.1 q.1.2.1)) hkK hhi
    have hTpos : 0 < T := by linarith
    have hY : 0 < detectorY a T := Real.rpow_pos_of_pos hTpos _
    exact hnorm (detectorX δ T) (detectorY a T) q.1.1 q.1.2.1 q.1.2.2 q.2.1 hY hkK
      (hsupp.trans (hupper.trans (by nlinarith)))

/- Complete actual-zero dichotomy: a long smooth detector, or a member of
the finite normalized powered short family at the original ordinate. -/
theorem smooth_long_or_short_powered_cover {σ a δ η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T → riemannZeta ρ = 0 →
      (∃ j ∈ smoothScaleIndices (detectorY a T*(Real.log T)^2),
        T^(smoothingExponent a/2) < (2 : ℝ)^j ∧
        (1/(24*Real.log T) : ℝ) ≤ ‖smoothDetectorBlock ρ (detectorX δ T) (detectorY a T) j‖) ∨
      (∃ q ∈ smoothPoweredIndices a δ T,
        (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ≤
          ‖detectingPolynomial (smoothPoweredFamilyScale q) (smoothPoweredFamilyCoefficient η a δ T q) ρ.im‖) := by
  have ha : 0 < a := by linarith [hw.a_low]
  filter_upwards [smooth_long_or_short_Taylor_cover hw hδ.le hδ',
    short_scale_bounded_power ha hδ,
    exists_normalizedSmoothPowered_height hη (smoothPowerBound a δ)] with T hcover hpower hheight
  intro ρ hβ hβ' hγ hγ' hzero
  rcases hcover ρ hβ hβ' hγ hγ' hzero with hlong | ⟨p, hp, hlo, hhi, hdet⟩
  · exact Or.inl hlong
  · have hc : smoothingExponent a/2 = 3*a/4 := by unfold smoothingExponent; ring
    obtain ⟨k, hk, hkK, hklo, hkhi⟩ := hpower (smoothHalfScale p.1 p.2.1)
      hlo (by rw [← hc]; exact hhi)
    have hkK' : k ≤ smoothPowerBound a δ := hkK
    have hupper : (smoothHalfScale p.1 p.2.1 : ℝ)^k ≤ T^(smoothingExponent a) := by
      simpa only [smoothingExponent] using hkhi
    obtain ⟨l, hl, hh⟩ := hheight σ (detectorX δ T) (detectorY a T) ρ.im
      p.1 p.2.1 p.2.2 k hw.sigma_high.le (by omega) hkK' hdet
    refine Or.inr ⟨(p,k,l), ?_, hh⟩
    exact mem_smoothPoweredIndices.mpr ⟨hp, hk, hkK', Finset.mem_range.mp hl, hklo, hupper⟩

end Montgomery.RationalMoment.RightDetector.Physical
