import GuthMaynard.Improvement.CubicMaskedTailBudget
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

/-- The actual independently masked complex spatial mode sum is bounded by
its compact-ratio near mass plus a homogeneous negligible discarded error.
All masks and ordinary time densities vary after both constants. -/
theorem masked_spatial_near_tail_bound {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) {η : ℝ} (hη : 0 < η) :
    ∃ Cnear Ctail : ℝ, 0 < Cnear ∧ 0 < Ctail ∧
    ∀ (T L t₀ t₁ : ℝ) (S : Finset (ℤ × (ℤ × ℤ)))
      (μ : ℝ → ℝ) (A B C : Set ℝ),
      1 ≤ T → 0 < L → L ≤ T^(1+η) → t₀ ≤ t₁ → t₁-t₀ ≤ T →
      S ⊆ cubicModes (T^(1+η)/L) →
      MeasurableSet A → MeasurableSet B → MeasurableSet C →
      Measurable μ → (∀ t, 0 ≤ μ t) → Integrable μ → Integrable (fun t => μ t^2) →
      (∀ t, t ∉ Icc t₀ t₁ → μ t = 0) →
      (∀ m, Integrable (maskedSpatialCubicMode a μ L m A B C)) ∧
      (∀ m, IntegrableOn (maskedRadialNearMass μ A B C L (T^η) m)
        (Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l))) ∧
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ x : Triple, maskedSpatialCubicMode a μ L m A B C x)‖ ≤
        Cnear*L^3*(∑ m ∈ S, ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
          maskedRadialNearMass μ A B C L (T^η) m p) +
        Ctail*T^(-100:ℝ)*(u/l-l/u)^2*Real.sqrt (∫ t, μ t^2)^3 := by
  have hu : 0 < u := hl.trans_le hlu
  have hq : l/u ≤ u/l :=
    ((div_le_iff₀ hu).mpr (by simpa using hlu)).trans
      ((le_div_iff₀ hl).mpr (by simpa using hlu) : (1:ℝ) ≤ u/l)
  obtain ⟨Cnear,hCn,hn⟩ := masked_radial_near_bound ha hlu hs (l/u) (u/l) (l/u) (u/l)
  obtain ⟨Ctail,hCt,htail⟩ := masked_radial_discard_negligible ha hlu hs
    (l/u) (u/l) (l/u) (u/l) hq hq hη
  obtain ⟨_,_,hd⟩ := masked_radial_discard_integral_bound ha hlu hs
    (l/u) (u/l) (l/u) (u/l) hq hq 0
  refine ⟨Cnear,Ctail,hCn,hCt,?_⟩
  intro T L t₀ t₁ S μ A B C hT hL hLT ht hlen hS hA hB hC hm h0 hi h2 hsup
  have hTp : 0 < T := by linarith
  have hH : 0 < T^η := Real.rpow_pos_of_pos hTp _
  have hni := fun m => hn L (T^η) m μ A B C hA hB hC hm h0 hi
  have hdi := fun m => hd L (T^η) m μ A B C hH hA hB hC hm h0 hi
  refine ⟨fun m => maskedSpatialCubicMode_integrable ha.continuous hs hm h0 hi L m hA hB hC,
    fun m => (hni m).1,?_⟩
  have hmode (m : ℤ × (ℤ × ℤ)) :
      (∫ x : Triple, maskedSpatialCubicMode a μ L m A B C x) =
      (∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l), maskedRadialNear a μ A B C L (T^η) m p) +
      (∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l), radialDiscard a μ L (T^η) m p*ratioMaskProduct A B C p) := by
    rw [maskedSpatialCubicMode_radial_fubini ha hl hlu hs hm h0 hi L m hA hB hC]
    rw [← integral_add (hni m).2.1 (hdi m).1]
    apply integral_congr_ae
    filter_upwards with p
    exact masked_radial_near_discard a μ A B C L (T^η) m p
  have hnear :
      ‖(L:ℂ)^3*(∑ m ∈ S, ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        maskedRadialNear a μ A B C L (T^η) m p)‖ ≤
      Cnear*L^3*(∑ m ∈ S, ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        maskedRadialNearMass μ A B C L (T^η) m p) := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    calc
      _ ≤ L^3*(∑ m ∈ S, ‖∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
          maskedRadialNear a μ A B C L (T^η) m p‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ L^3*(∑ m ∈ S, Cnear*(∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
          maskedRadialNearMass μ A B C L (T^η) m p)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ => (hni m).2.2)) (by positivity)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hfar := htail T L t₀ t₁ S μ A B C hT hL hLT ht hlen hS hA hB hC hm h0 hi h2 hsup
  simp only [← pow_two] at hfar
  simp_rw [hmode]
  rw [Finset.sum_add_distrib,mul_add]
  exact (norm_add_le _ _).trans (add_le_add hnear hfar)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.masked_spatial_near_tail_bound
