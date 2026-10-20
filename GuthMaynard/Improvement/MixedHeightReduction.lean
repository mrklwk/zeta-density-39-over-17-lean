module
public import GuthMaynard.Improvement.MixedPoissonBridge
public import GuthMaynard.Improvement.UnequalHeightReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

set_option maxHeartbeats 800000 in
/-- Uniform tail closure for a fixed height-mass Fourier family. No tail
estimate or divisor bound is an input premise; the full family is explicit. -/
theorem mixed_height_reduction (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T : ℝ) (hT : 2 ≤ T) (f : 𝓢(ℝ, ℝ)) (R K M₁ M₂ M₃ : ℕ),
      (∀ x, 0 ≤ f x) → GMAffineIterationSupported f →
      GMAffineHeightFourierMassFamilyAtDepth T D 0 f →
      0 < K → K ≤ R → (R:ℝ) ≤ T^4 →
      0 < M₁ → 0 < M₂ → 0 < M₃ → M₁ ≤ R → M₂ ≤ K → M₃ ≤ R →
      gmAffineTransformIntegral f M₁ M₂ M₃ ≤ A*T^δ*
        ((R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2+(R:ℝ)*(K:ℝ)*
          (Real.sqrt (∫ x, f x^2)*Real.sqrt (gmAffineJ
            (unequalAdaptive T δ M₂ M₃ f (by linarith)) M₂))) := by
  have hη := gmAffineIterationEta_pos hδ
  obtain ⟨n, hn⟩ := exists_nat_mul_ge_of_pos (eta := gmAffineIterationEta δ) (A := 31) hη
  have hnreal : (31:ℝ) ≤ n := hn.trans (by
    have hu := gmAffineIterationEta_le_one δ
    have hn0 : (0:ℝ) ≤ n := by positivity
    nlinarith)
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1:ℝ) ≤ n by linarith)
  have hn20 : 20 ≤ n := by exact_mod_cast (show (20:ℝ) ≤ n by linarith)
  obtain ⟨Cdiv,hCdiv,hraw⟩ := mixed_two_poisson_raw hη
  let d := D (gmAffineIterationEta δ) n
  let a := gmAffineRegionIConstant n ^ 2
  let b := Cdiv*gmAffineRegionIICoreConstant
  let c := gmAffineRegionIITailMassConstant n Cdiv d+
    2*(16*(2:ℝ)^n*d*gmAffineRegionIIIKernelConstant n)^2
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := mul_nonneg hCdiv.le gmAffineRegionIICoreConstant_nonneg
  have hc : 0 ≤ c := add_nonneg (gmAffineRegionIITailMassConstant_nonneg n hCdiv.le) (by positivity)
  refine ⟨a+b+c+1,by positivity,?_⟩
  intro T hT f R K M₁ M₂ M₃ hf hs hp hK hKR hRT h₁ h₂ h₃ h₁R h₂K h₃R
  have hTp : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hR : 0 < R := hK.trans_le hKR
  have hQ : 1 ≤ T ^ gmAffineIterationEta δ := one_le_rpow_gmAffineIterationEta hδ hTone
  have hY : 0 < T ^ (6:ℕ) := by positivity
  have hQM := gmAffineIterationQ_mul_M_le_four_Y (delta := δ) hTone hRT
  have hXY := gmAffineFirstPoissonRadius_le_of_scale h₁R h₃
    (show 0 ≤ T ^ gmAffineIterationEta δ by positivity) hQM
  have hheight : GMAffineHeightFourierMassBound (gmAffineIterationEta δ) T n d f := by
    simpa [d] using hp (gmAffineIterationEta δ) hη n
  obtain ⟨Ctail,hCtail,hprod,hdecay⟩ := exists_gmAffineHeightDecayConstant hTp (hD _ _) hf hheight
  have hr := hraw n T (T ^ gmAffineIterationEta δ) (T ^ (6:ℕ)) Ctail f M₁ M₂ M₃ R K
    hn1 hTone hQ hY hCtail hf hs h₁ h₂ h₃ h₁R h₂K h₃R hXY hdecay
  have ht := (gmAffineRegionIITailRawBound_le_source n hη.le hTone hQ hY hCdiv.le
    hCtail f hf h₁ h₁R h₂ (h₂K.trans hKR) h₃ h₃R hRT hQM).trans
      (gmAffineRegionIITailSourceBound_le_heightMass hδ hT hCdiv.le f hf hprod hRT hn)
  have hh := (gmAffineRegionIIIRawBound_le_source n hn1 f hQ hY
    h₁ h₁R h₂ (h₂K.trans hKR) h₃ h₃R).trans
      (gmAffineRegionIIISourceBound_le_heightMass hT (hD _ _) f hf hRT hn20 hheight)
  have hlow := gmAffineIterationQ_cube_le hδ hTone
  have hcore := gmAffineIterationRegionIIScaleFactor_le hδ hT h₁R h₃ hRT
  let X := (R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2
  let Z := (R:ℝ)*(K:ℝ)*(Real.sqrt (∫ x, f x^2)*Real.sqrt
    (gmAffineJ (unequalAdaptive T δ M₂ M₃ f hTp) M₂))
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hmassX : (∫ x, f x)^2 ≤ X := by
    have hr1 : (1:ℝ) ≤ R := by exact_mod_cast hR
    have hk1 : (1:ℝ) ≤ K := by exact_mod_cast hK
    have hr2 : (1:ℝ) ≤ (R:ℝ)^2 := one_le_pow₀ hr1
    have hk4 : (1:ℝ) ≤ (K:ℝ)^4 := one_le_pow₀ hk1
    have hprod1 : (1:ℝ) ≤ (R:ℝ)^2*(K:ℝ)^4 := one_le_mul_of_one_le_of_one_le hr2 hk4
    exact (le_mul_of_one_le_left (sq_nonneg _) hprod1)
  have hTδ : 1 ≤ T^δ := Real.one_le_rpow hTone hδ.le
  have hbound : gmAffineTransformIntegral f M₁ M₂ M₃ ≤
      a*T^δ*X+b*T^δ*Z+c*(∫ x, f x)^2 := by
    apply hr.trans
    have hl := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlow hX) ha
    have hc' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcore hZ) hb
    have hsum := add_le_add (add_le_add hl hc') (add_le_add ht hh)
    convert hsum using 1 <;> dsimp only [a,b,c,X,Z,unequalAdaptive] <;> ring
  change gmAffineTransformIntegral f M₁ M₂ M₃ ≤ (a+b+c+1)*T^δ*(X+Z)
  apply hbound.trans
  have hcsmall : c*(∫ x, f x)^2 ≤ c*T^δ*X := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (hmassX.trans (le_mul_of_one_le_left hX hTδ)) hc
  calc
    _ ≤ a*T^δ*X+b*T^δ*Z+c*T^δ*X := add_le_add le_rfl hcsmall
    _ = (a+c)*T^δ*X+b*T^δ*Z := by ring
    _ ≤ (a+b+c+1)*T^δ*X+(a+b+c+1)*T^δ*Z := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (show a+c ≤ a+b+c+1 by linarith only [hb]) (by positivity)) hX)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (show b ≤ a+b+c+1 by linarith only [ha,hc]) (by positivity)) hZ)
    _ = _ := by ring


end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.mixed_height_reduction
