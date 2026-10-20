module
public import LaterPairs.PhysicalLongMeanCover
public import RetunedShortZeroCount
public import TraceAlternatives.CubePolynomialCountWindows

@[expose] public section

open Real Complex Filter MeasureTheory Finset Set
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density GuthMaynard.Improvement

/-- All actual short-detected zeros with analytic multiplicity, using the
proved sharp trace and full energy. The exact perturbation loss is73eta. -/
theorem smoothShortZeroCount_cube_bound {σ a η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hc : CubeCountWindow σ a) (hη : 0 < η)
    (hηa : η ≤ (1-3*a/2)/2) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothShortZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+73*η) := by
  classical
  obtain ⟨C,hC,hquad⟩ := cube_polynomial_count_window_loss hc hη hηa
  obtain ⟨Cb,hCb,hlocal⟩ := zeta_local_multiplicity_bound
  let K := smoothPowerBound a δ
  let D : ℝ := 144*(K:ℝ)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1+4*Cb*D*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),
    smoothPoweredFamily_admissible hw hη δ,
    smoothPoweredIndices_card_eventually hw δ,
    (tendsto_rpow_atTop hη).eventually_ge_atTop ((2:ℝ)^K),
    log_pow_eventually_le_rpow 3 hη] with T hT hadm hJ hconst hlogloss
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog2 : 0 ≤ Real.log (2*T) := Real.log_nonneg (by linarith)
  have hlogs : Real.log (2*T) ≤ 2*Real.log T := by
    rw [Real.log_mul (by norm_num) hTp.ne']
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<2) hT
    linarith
  let S := smoothShortZeroFinset η σ a δ T
  have hbin (k : ℤ) : (∑ ρ ∈ S.filter (fun ρ => ordinateBin ρ=k), (zetaMultiplicity ρ:ℝ)) ≤
      Cb*Real.log (2*T) := by
    have hs : S.filter (fun ρ => ordinateBin ρ=k) ⊆
        (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ=k) := by
      intro ρ hρ
      exact mem_filter.mpr ⟨smoothShortZeroFinset_subset η σ a δ T (mem_filter.mp hρ).1,(mem_filter.mp hρ).2⟩
    exact (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
      (hlocal σ T hw.sigma_low.le hT k)
  obtain ⟨R,hR,hcard,hsep,hrestore⟩ := weighted_separated_extraction S
    (fun ρ => (zetaMultiplicity ρ:ℝ)) (by positivity : 0 ≤ Cb*Real.log (2*T)) hbin
  let W := R.image Complex.im
  let J := smoothPoweredIndices a δ T
  let Wj := fun q => W.filter (fun t =>
    (smoothPoweredFamilyScale q:ℝ)^σ*T^(-2*η) ≤
      ‖detectingPolynomial (smoothPoweredFamilyScale q) (smoothPoweredFamilyCoefficient η a δ T q) t‖)
  have hWloc : ∀ t ∈ W, t ∈ Icc T (T+T) := by
    intro t ht
    obtain ⟨ρ,hρ,rfl⟩ := mem_image.mp ht
    obtain ⟨_,_,hlo,hhi⟩ := mem_zetaZeroFinset.mp (smoothShortZeroFinset_subset η σ a δ T (hR hρ))
    exact ⟨hlo,by linarith⟩
  have hper : ∀ q ∈ J, ((Wj q).card:ℝ) ≤ C*T^(3*a*(1-σ)+72*η) := by
    intro q hmem
    obtain ⟨hlo,hhi,_,hcoeff⟩ := hadm q hmem
    have hu : (smoothPoweredFamilyScale q:ℝ) ≤ T^(3*a/2+η) := by
      calc
        _ ≤ (2:ℝ)^K*T^(smoothingExponent a) := hhi
        _ ≤ T^η*T^(smoothingExponent a) := mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = _ := by rw [← Real.rpow_add hTp]; unfold smoothingExponent; congr 1; ring
    apply hquad T T (smoothPoweredFamilyScale q:ℝ) hT hlo hu (smoothPoweredFamilyCoefficient η a δ T q)
      (fun n _ => hcoeff n) (Wj q)
    · intro t ht
      exact hWloc t (mem_filter.mp ht).1
    · intro t ht u hu hne
      exact hsep t (mem_filter.mp ht).1 u (mem_filter.mp hu).1 hne
    · intro t ht
      simpa only [← detectingPolynomial_eq_boundedPolynomial] using (mem_filter.mp ht).2
  have hcover : W ⊆ J.biUnion Wj := by
    intro t ht
    obtain ⟨ρ,hρ,rfl⟩ := mem_image.mp ht
    obtain ⟨q,hq,hl⟩ := (mem_filter.mp (hR hρ)).2
    exact mem_biUnion.mpr ⟨q,hq,mem_filter.mpr ⟨mem_image.mpr ⟨ρ,hρ,rfl⟩,hl⟩⟩
  have hWcard : (W.card:ℝ) ≤ (J.card:ℝ)*(C*T^(3*a*(1-σ)+72*η)) := by
    calc
      _ ≤ ∑ q ∈ J, ((Wj q).card:ℝ) := by exact_mod_cast (Finset.card_le_card hcover).trans card_biUnion_le
      _ ≤ ∑ _q ∈ J, C*T^(3*a*(1-σ)+72*η) := sum_le_sum hper
      _ = _ := by simp
  have hrestore' : (smoothShortZeroCount η σ a δ T:ℝ) ≤ 2*(Cb*Real.log (2*T))*(W.card:ℝ) := by
    rw [← hcard] at hrestore
    simpa only [smoothShortZeroCount,Nat.cast_sum,S,W] using hrestore
  have hJ' : (J.card:ℝ) ≤ D*(Real.log T)^2 := hJ
  have hWcard' : (W.card:ℝ) ≤ (D*(Real.log T)^2)*(C*T^(3*a*(1-σ)+72*η)) :=
    hWcard.trans (mul_le_mul_of_nonneg_right hJ' (by positivity))
  calc
    _ ≤ 2*(Cb*Real.log (2*T))*(W.card:ℝ) := hrestore' 
    _ ≤ 2*(Cb*(2*Real.log T))*((D*(Real.log T)^2)*(C*T^(3*a*(1-σ)+72*η))) := by
      gcongr
    _ = (4*Cb*D*C)*((Real.log T)^3*T^(3*a*(1-σ)+72*η)) := by ring
    _ ≤ (4*Cb*D*C)*(T^η*T^(3*a*(1-σ)+72*η)) := by
      gcongr
    _ = (4*Cb*D*C)*T^(3*a*(1-σ)+73*η) := by rw [← Real.rpow_add hTp]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Montgomery.RationalMoment.RightDetector.Physical
