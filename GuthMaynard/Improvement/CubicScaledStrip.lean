module
public import GuthMaynard.Improvement.CubicDyadicAssembly

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Uniform, fully summed strip estimate at the intended T² and TL powers.
All affine, smoothing and dyadic estimates are discharged. The lower height
threshold is explicit; it is not a full centered trace theorem. -/
theorem cubic_scaled_strip (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ η C T₀ : ℝ, 0 < η ∧ η < (4:ℝ)/5 ∧ 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (T L : ℝ) (r₀ r : ℝ → ℝ) (A₀ : Set ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      T₀ ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T →
      MeasurableSet A₀ → Measurable r₀ → MemLp r₀ 2 → (∀ v, 0 ≤ r₀ v) →
      Measurable r → Integrable (fun x => r x^2) → Integrable (fun x => r x^4) →
      (∀ x, 0 ≤ r x) → (∀ x, x ∉ Icc c d → r x = 0) →
      (∀ m ∈ S, m.1 ∈ poissonModes (T^(1+η)/L) ∧
        m.2.1 ∈ poissonModes (T^(1+η)/L) ∧ m.2.2 ∈ poissonModes (T^(1+η)/L)) →
      IntegrableOn (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L (T^η) m v) (Icc a b) ∧
      L^3*(∫ v in Icc a b, A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L (T^η) m v) ≤
        C*T^ε*Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b))*
          (T^2*(∫ x, r x^2)+T*L*Real.sqrt (∫ x, r x^4)) := by
  obtain ⟨η,α,δ,hη,hη1,hα,hδ,hbudget⟩ := cubic_scale_choose_exponents hε
  obtain ⟨C,hC,hbound⟩ := cubic_dyadic_strip_assembly a b c d ha hab hc hcd hα
  obtain ⟨D,hD,hcount⟩ := cubicDyadicClasses_subpower hδ
  let q : ℝ := max 1 (1/a)
  have hq : 1 ≤ q := le_max_left _ _
  have hsmall : 0 < min 1 (c/4) := lt_min (by norm_num) (by positivity)
  obtain ⟨T₁,hT₁,hwidth⟩ := cubic_smoothing_width_eventually hη.le hη1 hq hsmall
  refine ⟨η,C*D,max 2 T₁,hη,hη1,mul_pos hC hD,le_max_left _ _,?_⟩
  intro T L r₀ r A₀ S hT₀ hLl hLu hA hr₀ hmem₀ hr₀0 hr hr2 hr4 hr0 hs hS
  have hT : 2 ≤ T := (le_max_left _ _).trans hT₀
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := (Real.rpow_pos_of_pos hTp _).trans_le hLl
  let U := T^(1+η)/L
  have hUp : 0 < U := by dsimp [U]; positivity
  have hH : 0 < T^η := Real.rpow_pos_of_pos hTp _
  have hid : T^(1+η) = T*T^η := by rw [Real.rpow_add hTp,Real.rpow_one]
  have hU : 1 ≤ U := by
    apply (le_div_iff₀ hLp).mpr
    have hh : 1 ≤ T^η := Real.one_le_rpow hT1 hη.le
    rw [hid]
    nlinarith
  have hUT : U ≤ T := cubic_truncation_height_le hT1 hη1.le hLl
  have hUT4 : U ≤ T^4 := hUT.trans (by nlinarith [sq_nonneg (T^2-1)])
  have hw : q*(T^η/L) ≤ min 1 (c/4) := by
    have hh := hwidth T L 1 1 ((le_max_right _ _).trans hT₀) hLl hLu le_rfl le_rfl hU
    simpa [cubicSmoothingWidth,div_eq_mul_inv,mul_assoc] using hh
  have hLU : L*U ≤ q*T^η*T := by
    have he : L*U = T*T^η := by dsimp [U]; rw [hid]; field_simp
    rw [he]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (mul_nonneg hH.le hTp.le)]
  obtain ⟨hi,hb⟩ := hbound T U L (T^η) r₀ r A₀ S hT hU hUT4 hLp hH
    (hw.trans (min_le_left _ _)) (hw.trans (min_le_right _ _)) hLU
    hA hr₀ hmem₀ hr₀0 hr hr2 hr4 hr0 hs hS
  refine ⟨hi,?_⟩
  have hM : 0 ≤ ∫ x, r x^2 := integral_nonneg (fun x => sq_nonneg _)
  have hcard : ((cubicDyadicClasses U).card:ℝ) ≤ D*T^δ :=
    (hcount U hU).trans (by gcongr)
  have he₁ : L^2*T^η*U^2 = T^(3*η)*T^2 := by
    have hh : L^2*T^η*U^2 = T^η*(T^(1+η))^2 := by dsimp [U]; field_simp
    rw [hh,← Real.rpow_natCast (T^(1+η)) 2,← Real.rpow_mul hTp.le,
      ← Real.rpow_add hTp,← Real.rpow_natCast T 2,← Real.rpow_add hTp]
    congr 1
    norm_num
    ring
  have he₂ : L^2*T^η*U = T^(2*η)*T*L := by
    have hh : L^2*T^η*U = (T^η*T^(1+η))*L := by dsimp [U]; field_simp
    rw [hh,← Real.rpow_add hTp]
    have hp : T^(η+(1+η)) = T^(2*η)*T := by
      calc
        _ = T^(2*η+1) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hTp,Real.rpow_one]
    rw [hp]
  let A := ∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b)
  have he : L^3*(C*((cubicDyadicClasses U).card:ℝ)*(T^η/L)*Real.sqrt A*Real.sqrt (T^α)*
      (U^2*(∫ x, r x^2)+U*Real.sqrt (∫ x, r x^4))) =
      C*((cubicDyadicClasses U).card:ℝ)*T^(α/2)*Real.sqrt A*
      (T^(3*η)*T^2*(∫ x, r x^2)+T^(2*η)*T*L*Real.sqrt (∫ x, r x^4)) := by
    rw [cubic_affine_sqrt_exponent hT1 α,← he₁,← he₂]
    field_simp
  calc
    _ ≤ L^3*(C*((cubicDyadicClasses U).card:ℝ)*(T^η/L)*Real.sqrt A*Real.sqrt (T^α)*
        (U^2*(∫ x, r x^2)+U*Real.sqrt (∫ x, r x^4))) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := he
    _ ≤ C*(D*T^δ)*T^(α/2)*Real.sqrt A*
        (T^(3*η)*T^2*(∫ x, r x^2)+T^(2*η)*T*L*Real.sqrt (∫ x, r x^4)) := by gcongr
    _ = C*D*(T^δ*T^(α/2)*Real.sqrt A*
        (T^(3*η)*T^2*(∫ x, r x^2)+T^(2*η)*T*L*Real.sqrt (∫ x, r x^4))) := by ring
    _ ≤ C*D*(T^ε*Real.sqrt A*(T^2*(∫ x, r x^2)+T*L*Real.sqrt (∫ x, r x^4))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_pos hC hD).le
      exact cubic_box_epsilon_absorption hT1 hη.le hLp.le hM hbudget
    _ = _ := by ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.cubic_scaled_strip
