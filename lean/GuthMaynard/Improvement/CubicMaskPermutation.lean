import GuthMaynard.Improvement.RetainedRadialAssembly
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

def cycleCubicMode (m : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) := (m.2.1,m.2.2,m.1)
def cycleSpatial : Triple ≃ᵐ Triple := MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc

def maskedSpatialCubicMode (a : ℝ → ℂ) (μ : ℝ → ℝ) (L : ℝ)
    (m : ℤ × (ℤ × ℤ)) (A B C : Set ℝ) (x : Triple) : ℂ :=
  A.indicator (fun _ : ℝ => (1:ℂ)) (mellinFrequency x.2.2-mellinFrequency x.1) *
    B.indicator (fun _ : ℝ => (1:ℂ)) (mellinFrequency x.1-mellinFrequency x.2.1) *
    C.indicator (fun _ : ℝ => (1:ℂ)) (mellinFrequency x.2.1-mellinFrequency x.2.2) *
    spatialCubicMode a μ L m x.1 x.2.1 x.2.2

theorem cycleSpatial_preserving : MeasurePreserving cycleSpatial volume volume :=
  (measurePreserving_prodAssoc volume volume volume).comp Measure.measurePreserving_swap

theorem cycleCubicMode_injective : Function.Injective cycleCubicMode := by
  rintro ⟨m₁,m₂,m₃⟩ ⟨n₁,n₂,n₃⟩ h
  simpa only [cycleCubicMode,Prod.mk.injEq,and_assoc,and_left_comm,and_comm] using h

/-- Cyclic reordering preserves the exact complex oscillatory integrand,
rotating the three independently designated frequency masks with it. -/
theorem maskedSpatialCubicMode_cycle (a : ℝ → ℂ) (μ : ℝ → ℝ) (L : ℝ)
    (m : ℤ × (ℤ × ℤ)) (A B C : Set ℝ) (x : Triple) :
    maskedSpatialCubicMode a μ L (cycleCubicMode m) B C A (cycleSpatial x) =
      maskedSpatialCubicMode a μ L m A B C x := by
  have he : cycleSpatial x = (x.2.1,x.2.2,x.1) := rfl
  rw [he]
  unfold maskedSpatialCubicMode spatialCubicMode cycleCubicMode
  dsimp only
  have hp : -L*((m.2.1:ℝ)*x.2.1+(m.2.2:ℝ)*x.2.2+(m.1:ℝ)*x.1) =
      -L*((m.1:ℝ)*x.1+(m.2.1:ℝ)*x.2.1+(m.2.2:ℝ)*x.2.2) := by ring
  rw [hp]
  ring

theorem maskedSpatialCubicMode_integrable {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : Continuous a) {l u : ℝ} (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    Integrable (maskedSpatialCubicMode a μ L m A B C) := by
  have hmf : Measurable mellinFrequency := by unfold mellinFrequency; fun_prop
  have hsp := spatialCubicMode_measurable ha.measurable hi L m
  have hmasks : Measurable (maskedSpatialCubicMode a μ L m A B C) := by
    have hAi : Measurable (A.indicator (fun _ : ℝ => (1:ℂ))) := measurable_const.indicator hA
    have hBi : Measurable (B.indicator (fun _ : ℝ => (1:ℂ))) := measurable_const.indicator hB
    have hCi : Measurable (C.indicator (fun _ : ℝ => (1:ℂ))) := measurable_const.indicator hC
    unfold maskedSpatialCubicMode
    fun_prop
  apply (spatialCubicMode_integrable ha hs hm h0 hi L m).norm.mono' hmasks.aestronglyMeasurable
  filter_upwards with x
  unfold maskedSpatialCubicMode
  by_cases hAx : mellinFrequency x.2.2-mellinFrequency x.1 ∈ A <;>
    by_cases hBx : mellinFrequency x.1-mellinFrequency x.2.1 ∈ B <;>
    by_cases hCx : mellinFrequency x.2.1-mellinFrequency x.2.2 ∈ C <;>
    simp [hAx,hBx,hCx]

/-- Exact integral equality before any absolute-value estimate. The separate
integrability theorem supplies existence for the ordinary analytic inputs. -/
theorem maskedSpatialCubicMode_integral_cycle (a : ℝ → ℂ) (μ : ℝ → ℝ) (L : ℝ)
    (m : ℤ × (ℤ × ℤ)) (A B C : Set ℝ) :
    (∫ x : Triple, maskedSpatialCubicMode a μ L m A B C x) =
      ∫ x : Triple, maskedSpatialCubicMode a μ L (cycleCubicMode m) B C A x := by
  rw [← cycleSpatial_preserving.integral_comp' (maskedSpatialCubicMode a μ L (cycleCubicMode m) B C A)]
  simp only [maskedSpatialCubicMode_cycle]

theorem maskedSpatialCubicMode_sum_cycle (a : ℝ → ℂ) (μ : ℝ → ℝ) (L : ℝ)
    (S : Finset (ℤ × (ℤ × ℤ))) (A B C : Set ℝ) :
    (∑ m ∈ S, ∫ x : Triple, maskedSpatialCubicMode a μ L m A B C x) =
      ∑ m ∈ S.image cycleCubicMode, ∫ x : Triple, maskedSpatialCubicMode a μ L m B C A x := by
  rw [Finset.sum_image (fun _ _ _ _ h => cycleCubicMode_injective h)]
  exact Finset.sum_congr rfl (fun m _ => maskedSpatialCubicMode_integral_cycle a μ L m A B C)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.cycleSpatial_preserving
#print axioms GuthMaynard.Improvement.cycleCubicMode_injective
#print axioms GuthMaynard.Improvement.maskedSpatialCubicMode_cycle
#print axioms GuthMaynard.Improvement.maskedSpatialCubicMode_integrable
#print axioms GuthMaynard.Improvement.maskedSpatialCubicMode_integral_cycle
#print axioms GuthMaynard.Improvement.maskedSpatialCubicMode_sum_cycle
