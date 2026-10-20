module
/- Adapted from the verified Density.DetectorGamma and DetectorError residue
bounds. The actual residue definition is reused, with independent X and Y;
the final specialization uses the short parameters, not the old firstDetectorX. -/
public import GuthMaynard.Improvement.ShortDetectorGamma
public import MathCollab.Density.DetectorError

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- The crossed pole lies in the same audited compact Gamma strip down to
beta=9/13. This estimate needs only a nonzero large ordinate. -/
theorem short_norm_Gamma_one_sub_zero_le {ρ : ℂ} (hβ : 9/13 ≤ ρ.re)
    (hβ' : ρ.re ≤ 1) (hγ : 1 ≤ |ρ.im|) :
    ‖Complex.Gamma (1-ρ)‖ ≤ 12*(1+|ρ.im|)*Real.exp (-|ρ.im|) := by
  have he : 1-ρ = ((1-ρ.re : ℝ) : ℂ)+((-ρ.im : ℝ) : ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  rw [he]
  simpa [GammaBounds.stripPoint] using GammaBounds.norm_Gamma_compactStrip_le_exp
    (a := 1-ρ.re) (t := -ρ.im) (by linarith) (by linarith) (by simpa using hγ)

/-- Generic actual residue estimate with independent X and Y, and no zeta
zero, pointwise growth, or moment premise. -/
theorem short_norm_detectorResidue_le {ρ : ℂ} {X Y : ℝ}
    (hX : 0 ≤ X) (hY : 0 < Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hγ : 1 ≤ |ρ.im|) :
    ‖detectorResidue ρ X Y‖ ≤
      24*Real.sqrt X*Y^(1-ρ.re)*(1+|ρ.im|)*Real.exp (-|ρ.im|) := by
  have hm := norm_zetaMollifier_le_two_sqrt (s := 1) hX (by norm_num)
  have hg := short_norm_Gamma_one_sub_zero_le hβ hβ' hγ
  dsimp [detectorResidue]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ Y^(1-ρ.re)*(12*(1+|ρ.im|)*Real.exp (-|ρ.im|))*(2*Real.sqrt X) := by gcongr
    _ = _ := by ring

/-- Uniform exponential majorant for the actual short-mollifier residue.
Both signs of the ordinate are covered; X and Y have their exact short values. -/
theorem short_detector_residue_bound {ρ : ℂ} {H : ℝ}
    (hH : 1 ≤ H) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hγ : H ≤ |ρ.im|) (hγ' : |ρ.im| ≤ 2*H) :
    ‖detectorResidue ρ (2*H^((1:ℝ)/100)) (H^((1:ℝ)/2))‖ ≤
      72*H^3*Real.exp (-H) := by
  have hHpos : 0 < H := by linarith
  have hX : 0 ≤ 2*H^((1:ℝ)/100) := by positivity
  have hXle : 2*H^((1:ℝ)/100) ≤ 2*H := by
    have hp := Real.rpow_le_rpow_of_exponent_le hH (by norm_num : (1/100 : ℝ) ≤ 1)
    simpa using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  have hm := (norm_zetaMollifier_le_cutoff (2*H^((1:ℝ)/100)) (s := 1) (by norm_num)).trans
    ((Nat.floor_le hX).trans hXle)
  have hg := short_norm_Gamma_one_sub_zero_le hβ hβ' (hH.trans hγ)
  have hp : (H^((1:ℝ)/2))^(1-ρ.re) ≤ H := by
    rw [← Real.rpow_mul hHpos.le]
    simpa using Real.rpow_le_rpow_of_exponent_le hH (by linarith : (1/2:ℝ)*(1-ρ.re) ≤ 1)
  have hexp : Real.exp (-|ρ.im|) ≤ Real.exp (-H) := Real.exp_le_exp.mpr (by linarith)
  dsimp [detectorResidue]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < H^((1:ℝ)/2))]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ H*(12*(3*H)*Real.exp (-H))*(2*H) := by
      apply mul_le_mul _ hm (norm_nonneg _) (by positivity)
      apply mul_le_mul hp _ (norm_nonneg _) (by positivity)
      exact hg.trans (by gcongr; linarith)
    _ = _ := by ring

/-- Every positive target has one height threshold before all actual rho in
the slab. No zero or unproved twisted-moment assumption is involved. -/
theorem short_detector_residue_eventually_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ H : ℝ in atTop, ∀ ρ : ℂ,
      9/13 ≤ ρ.re → ρ.re ≤ 1 → H ≤ |ρ.im| → |ρ.im| ≤ 2*H →
      ‖detectorResidue ρ (2*H^((1:ℝ)/100)) (H^((1:ℝ)/2))‖ < δ := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul 72
  simp only [mul_zero] at ht
  have he : ∀ᶠ H : ℝ in atTop, 72*H^3*Real.exp (-H) < δ := by
    simpa only [mul_zero, mul_assoc] using ht.eventually (gt_mem_nhds hδ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), he] with H hH hsmall
  intro ρ hβ hβ' hγ hγ'
  exact (short_detector_residue_bound hH hβ hβ' hγ hγ').trans_lt hsmall

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.short_norm_Gamma_one_sub_zero_le
#print axioms GuthMaynard.Improvement.short_norm_detectorResidue_le
#print axioms GuthMaynard.Improvement.short_detector_residue_bound
#print axioms GuthMaynard.Improvement.short_detector_residue_eventually_small
