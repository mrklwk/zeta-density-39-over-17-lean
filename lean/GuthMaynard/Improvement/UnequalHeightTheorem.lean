module
public import GuthMaynard.Improvement.UnequalHeightReduction
public import GuthMaynard.Improvement.SparseAffineInput
public import GuthMaynard.Improvement.UniformReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Apply the verified sparse affine theorem to the actual adaptive source
smoothing, uniformly even in the internal epsilon parameter. -/
theorem adaptive_sparse_affine (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ (T δ : ℝ) (hT : 8 ≤ T) (f : 𝓢(ℝ, ℝ)) (R K : ℕ),
      (∀ x, 0 ≤ f x) → GMAffineSourceSupported f →
      GMAffineHeightFourierMassFamilyAtDepth T D 0 f →
      0 < K → (K:ℝ) ≤ T^4 →
      gmAffineJ (unequalAdaptive T δ K R f (by linarith)) K ≤
        B*T^ε*((K:ℝ)^6*(∫ x, f x)^2+(K:ℝ)^4*(∫ x, f x^2)) := by
  obtain ⟨B,hB,hbound⟩ := sparse_affine_all_heights
    (fun β n => 2*D β n) (fun β n => mul_nonneg (by norm_num) (hD β n)) hε
  refine ⟨16*B,by positivity,?_⟩
  intro T δ hT f R K hf hs hp hK hKT
  have hTp : 0 < T := by linarith
  let Q := T ^ gmAffineIterationEta δ
  have hQ : 0 < Q := Real.rpow_pos_of_pos hTp _
  let S := gmAffineSecondPoissonCutoff T Q K R/Q
  have hS : 0 < S := div_pos (gmAffineSecondPoissonCutoff_pos hTp hQ) hQ
  have hTS : T ≤ S := gmAffineSecondPoissonSmoothingScale_ge hQ
  let ft := gmAffineTildeSchwartz S hS f
  have hft : ∀ x, 0 ≤ ft x := gmAffineTildeSchwartz_nonneg S hS f hf
  have hwidth : 2/S ≤ (1/4:ℝ) := (div_le_iff₀ hS).mpr (by linarith only [hT,hTS])
  have hsft : GMAffineSupportedOn (1/4:ℝ) (9/4) ft :=
    (gmAffineTildeSchwartz_supportedOn hS f hs.supportedOn).mono (by linarith) (by linarith)
  have hpft : GMAffineHeightFourierMassFamilyAtDepth T (fun β n => 2*D β n) 0 ft := by
    have h := gmAffineTildeSchwartz_heightFourierMassFamilyAtDepth_succ hTp.le hS D hD f hf hp
    simpa only [GMAffineHeightFourierMassFamilyAtDepth,Nat.zero_add,pow_zero,pow_one,one_mul] using h
  have hmain := hbound T ft K (by linarith) hft hsft hpft hK hKT
  have hw := gmAffineTildeSchwartz_weighted_norms_le_sixteen hS f hf (le_refl K)
  have hb := hmain.trans (mul_le_mul_of_nonneg_left hw (by positivity))
  simpa only [ft,S,Q,unequalAdaptive,mul_assoc,mul_left_comm,mul_comm] using hb

set_option maxHeartbeats 600000 in
/-- The strengthened unequal-scale estimate for the source's canonical
support/shell convention and any fixed height-mass Fourier family. All
Poisson, divisor, tail and adaptive smoothing premises are discharged. -/
theorem unequal_height_affine (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (f : 𝓢(ℝ, ℝ)) (R K : ℕ),
      2 ≤ T → (∀ x, 0 ≤ f x) → GMAffineSourceSupported f →
      GMAffineHeightFourierMassFamilyAtDepth T D 0 f →
      0 < K → K ≤ R → (R:ℝ) ≤ T^4 →
      gmAffineTransformIntegral f R K R ≤ C*T^ε*
        ((R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2+(R:ℝ)*(K:ℝ)^3*(∫ x, f x^2)) := by
  obtain ⟨A,hA,hP⟩ := unequal_height_reduction D hD (δ := ε/2) (by positivity)
  obtain ⟨B,hB,hF⟩ := adaptive_sparse_affine D hD hε
  let C := 2*A*Real.sqrt (B+1)+36992*(8:ℝ)^24
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T f R K hT hf hs hp hK hKR hRT
  have hTp : 0 < T := by linarith
  have hR : 0 < R := hK.trans_le hKR
  have hr1 : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hk1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hkr : (K:ℝ) ≤ R := by exact_mod_cast hKR
  have hKT : (K:ℝ) ≤ T^4 := hkr.trans hRT
  have hmass : 0 ≤ ∫ x, f x := integral_nonneg hf
  have hL2 : 0 ≤ ∫ x, f x^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hpow : 1 ≤ T^ε := Real.one_le_rpow (by linarith) hε.le
  let W := (R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2+(R:ℝ)*(K:ℝ)^3*(∫ x, f x^2)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  by_cases hlarge : 8 ≤ T
  · have hq := hF T (ε/2) hlarge f R K hf hs hp hK hKT
    have hF' : gmAffineJ (unequalAdaptive T (ε/2) K R f hTp) K ≤
        ((B+1)*T^ε)*((K:ℝ)^6*(∫ x, f x)^2+(K:ℝ)^4*(Real.sqrt (∫ x, f x^2))^2) := by
      rw [Real.sq_sqrt hL2]
      exact hq.trans (by gcongr; linarith)
    have hP' := hP T hT f R K hf hs.iterationSupported hp hK hKR hRT
    have hclosed := unequal_reduction_of_estimates
      (show 0 ≤ A*T^(ε/2) by positivity)
      (show 1 ≤ (B+1)*T^ε by nlinarith only [hB,hpow])
      (Nat.cast_nonneg K) hkr hmass (Real.sqrt_nonneg _)
      (by simpa only [mul_assoc] using hP') hF'
    have hsqrt : Real.sqrt ((B+1)*T^ε) = Real.sqrt (B+1)*T^(ε/2) := by
      rw [Real.sqrt_mul (by positivity)]
      congr 1
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul hTp.le]
      congr 1
      ring
    have hpows : T^(ε/2)*T^(ε/2) = T^ε := by
      rw [← Real.rpow_add hTp]
      congr 1
      ring
    have hfinal : gmAffineTransformIntegral f R K R ≤ 2*A*Real.sqrt (B+1)*T^ε*W := by
      apply hclosed.trans_eq
      rw [hsqrt]
      unfold unequalScaleBound
      rw [Real.sq_sqrt hL2]
      dsimp only [W]
      calc
        _ = 2*A*Real.sqrt (B+1)*(T^(ε/2)*T^(ε/2))*
          ((R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2+(R:ℝ)*(K:ℝ)^3*(∫ x, f x^2)) := by ring
        _ = _ := by rw [hpows]
    exact hfinal.trans (by
      apply mul_le_mul_of_nonneg_right _ hW
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact le_add_of_nonneg_right (by positivity))
  · have hT8 : T ≤ 8 := le_of_lt (lt_of_not_ge hlarge)
    have hR8 : (R:ℝ)^6 ≤ (8:ℝ)^24 := by
      calc
        _ ≤ ((8:ℝ)^4)^6 := by gcongr; exact hRT.trans (by gcongr)
        _ = _ := by norm_num
    have hf2 : Integrable (fun x => f x^2) :=
      (memLp_two_iff_integrable_sq f.continuous.aestronglyMeasurable).1 (f.memLp 2)
    have hcrude := gmAffineTransformIntegral_le_crude hf2
      (mem_gmAffineScaleTriples.mpr ⟨hR,le_rfl,hK,hKR,hR,le_rfl⟩)
    have hL2W : (∫ x, f x^2) ≤ W := by
      have hcoef : (1:ℝ) ≤ (R:ℝ)*(K:ℝ)^3 :=
        one_le_mul_of_one_le_of_one_le hr1 (one_le_pow₀ hk1)
      exact (le_mul_of_one_le_left hL2 hcoef).trans
        (le_add_of_nonneg_left (by positivity))
    calc
      _ ≤ 36992*(8:ℝ)^24*(∫ x, f x^2) := hcrude.trans (by gcongr)
      _ ≤ 36992*(8:ℝ)^24*W := mul_le_mul_of_nonneg_left hL2W (by positivity)
      _ ≤ C*T^ε*W := by
        apply mul_le_mul_of_nonneg_right _ hW
        calc
          _ ≤ C := le_add_of_nonneg_left (by positivity)
          _ ≤ C*T^ε := le_mul_of_one_le_right hC.le hpow

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.adaptive_sparse_affine
#print axioms GuthMaynard.Improvement.unequal_height_affine
