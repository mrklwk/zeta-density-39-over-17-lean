module
public import GuthMaynard.Improvement.ShortDetectorPowerScales

@[expose] public section

open Real Complex Set Filter MathCollab.Density
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
namespace GuthMaynard.Improvement

/-- All powers and pieces are included before choosing sigma or a zero. -/
def shortPoweredDetectorIndices (T : ℝ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (fixedShortDetectorIndices T).product ((Finset.Icc 1 100).product (Finset.range 100))

def shortPoweredDetectorScale (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  2^p.2.2*(2^p.1.1)^p.2.1

def shortPoweredDetectorFamilyCoeff (η T : ℝ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ → ℂ :=
  shortNormalizedPoweredCoefficient η T (2^p.1.1) p.1.2 p.2.1

theorem shortPoweredDetectorIndices_card_le {T : ℝ}
    (hcard : ((fixedShortDetectorIndices T).card:ℝ) ≤ 60*(Real.log T)^2) :
    ((shortPoweredDetectorIndices T).card:ℝ) ≤ 600000*(Real.log T)^2 := by
  simp only [shortPoweredDetectorIndices]
  norm_num
  nlinarith

/-- Actual short detection yields a bounded-coefficient powered family in the
full target window, without moving the ordinate. No counting estimate is assumed. -/
theorem shortPoweredDetectorFamily_cover {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      ((shortPoweredDetectorIndices T).card:ℝ) ≤ 600000*(Real.log T)^2 ∧
      ∀ (a σ : ℝ) (ρ : ℂ), 3/4 ≤ a → a ≤ 4/5 →
        0 ≤ σ → σ ≤ ρ.re → ρ.re ≤ 1 → 1/3 ≤ ‖shortFiniteDetector ρ T‖ →
        ∃ p ∈ shortPoweredDetectorIndices T,
          T^a ≤ (shortPoweredDetectorScale p:ℝ) ∧
          (shortPoweredDetectorScale p:ℝ) ≤ (2:ℝ)^99*T^(3*a/2) ∧
          2*(shortPoweredDetectorScale p:ℝ) ≤ T^2 ∧
          (shortPoweredDetectorScale p:ℝ)^σ*T^(-2*η) ≤
            ‖detectingPolynomial (shortPoweredDetectorScale p)
              (shortPoweredDetectorFamilyCoeff η T p) ρ.im‖ := by
  filter_upwards [eventually_gt_atTop (1:ℝ), shortFiniteDetector_fixed_family_eventually,
    short_detector_power_buffer_eventually, exists_shortNormalizedPowered_height hη]
    with T hT hf hb hh
  refine ⟨shortPoweredDetectorIndices_card_le hf.1, ?_⟩
  intro a σ ρ ha ha' hσ hσβ hβ hlarge
  obtain ⟨q,hq,hlo,hhi,hd⟩ := hf.2 σ ρ hσ hσβ hβ hlarge
  obtain ⟨k,hk,hk100,hklo,hkhi⟩ := short_detector_power_exists hT
    (by linarith) (by linarith) hlo hhi.le (hb a ha ha').1
  obtain ⟨ℓ,hℓ,hheight⟩ := hh σ ρ.im (2^q.1) q.2 k (by positivity)
    hσ (hσβ.trans hβ) hk hk100 hd
  have hs := short_detector_power_piece_bounds hk100 (Finset.mem_range.mp hℓ)
    hklo hkhi (hb a ha ha').2
  refine ⟨(q,(k,ℓ)), Finset.mem_product.mpr ⟨hq, Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hk,hk100⟩, Finset.mem_range.mpr (by change ℓ < 100; have := Finset.mem_range.mp hℓ; omega)⟩⟩,
    hs.1, hs.2.1, hs.2.2, hheight⟩

/-- Uniform coefficient normalization for every eligible family piece. -/
theorem shortPoweredDetectorFamily_coefficients {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ p ∈ shortPoweredDetectorIndices T,
      2*(shortPoweredDetectorScale p:ℝ) ≤ T^2 →
      ∀ n ∈ Finset.Ioc (shortPoweredDetectorScale p) (2*shortPoweredDetectorScale p),
        ‖shortPoweredDetectorFamilyCoeff η T p n‖ ≤ 1 := by
  filter_upwards [shortNormalizedPoweredCoefficient_eventually hη (show 0 < (100:ℕ) by norm_num)]
    with T hT
  intro p hp hscale n hn
  have hk := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_product.mp hp).2).1).2
  have hn' : (n:ℝ) ≤ 2*(shortPoweredDetectorScale p:ℝ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).2
  exact hT (2^p.1.1) p.1.2 p.2.1 n (by positivity) hk (hn'.trans hscale)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.shortPoweredDetectorIndices_card_le
#print axioms GuthMaynard.Improvement.shortPoweredDetectorFamily_cover
#print axioms GuthMaynard.Improvement.shortPoweredDetectorFamily_coefficients
