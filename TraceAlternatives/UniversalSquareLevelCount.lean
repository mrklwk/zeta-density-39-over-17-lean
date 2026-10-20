module
public import TraceAlternatives.UniversalNativeLevelCount
public import TraceAlternatives.SquareLevelMonomial
public import DensityEnergyGM.PoweredLargeValues

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- Actual integer-square level count in the high-amplitude range.
The complementary range is retained explicitly in the short-S2 estimate. -/
theorem universal_square_level_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (M : ℕ) (T U : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → 2 ≤ T → (M:ℝ)^2 ≤ T → 0 < U →
        D*T^ε*(M:ℝ)^6 ≤ U^8 →
        (∀ n ∈ Ioc M (2*M), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, U ≤ ‖dirichletPoly M a t‖) →
        (W.card:ℝ) ≤ C*T^ε*((M:ℝ)^4*U^(-4:ℝ)+
          T^(2/3:ℝ)*(M:ℝ)^(16/3:ℝ)*U^(-8:ℝ)+
          T^(3/5:ℝ)*(M:ℝ)^(72/5:ℝ)*U^(-96/5:ℝ)) := by
  let ν : ℝ := ε/100
  have hν : 0 < ν := by dsimp only [ν]; positivity
  obtain ⟨A,hA,hCoeff⟩ := finitePowCoeff_bound_uniform 2 ν hν
  obtain ⟨C₀,D₀,hC₀,hD₀,hCount⟩ := universal_native_quadratic_level_count ν hν
  let B : ℝ := max 1 (2*A*(4:ℝ)^ν)
  let C : ℝ := 1024*C₀*(2:ℝ)^ν*B^10
  let D : ℝ := 8*D₀*(2:ℝ)^ν*B^4
  have hB : 1 ≤ B := le_max_left _ _
  have hBp : 0 < B := by linarith
  refine ⟨C,D,by dsimp only [C]; positivity,by dsimp only [D]; positivity,?_⟩
  intro M T U a W hM hT hMT hU hCut ha hSep hBase hLarge
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hMp : (0:ℝ) < M := by exact_mod_cast hM
  let d : ℝ := 2*(A*((2^2*M^2:ℕ):ℝ)^ν)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hDen : 0 < A*((2^2*M^2:ℕ):ℝ)^ν := by positivity
  obtain ⟨r,hr,W',hsub,hcard,hLarge'⟩ :=
    extract_normalized_finite_powered_block M 2 a 0 A ν U W hM (by norm_num)
      hU.le hDen (by
        intro t ht
        simpa [dirichletPoly,dyadicInterval,mul_comm] using hLarge t ht)
  let Q : ℕ := 2^r*M^2
  let V : ℝ := U^2/d
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hV : 0 < V := by dsimp only [V]; positivity
  have hQle : (Q:ℝ) ≤ 2*(M:ℝ)^2 := by
    have hr1 : r ≤ 1 := by have := mem_range.mp hr; omega
    have hp : 2^r ≤ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hr1
    dsimp only [Q]
    exact_mod_cast Nat.mul_le_mul_right (M^2) hp
  have hdForm : d = (2*A*(4:ℝ)^ν)*((M:ℝ)^2)^ν := by
    dsimp only [d]
    have hc : ((2^2*M^2:ℕ):ℝ) = 4*(M:ℝ)^2 := by push_cast; norm_num
    rw [hc,Real.mul_rpow (by norm_num) (sq_nonneg _)]
    ring_nf
  have hdP : d ≤ B*T^ν := by
    rw [hdForm]
    exact mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow (sq_nonneg _) hMT hν.le) (by positivity) hBp.le
  have hP : 1 ≤ B*T^ν := one_le_mul_of_one_le_of_one_le hB
    (Real.one_le_rpow hT1 hν.le)
  have hPow (k : ℕ) : (B*T^ν)^k = B^k*T^(ν*k) := by
    rw [mul_pow,← Real.rpow_natCast (T^ν),← Real.rpow_mul hTp.le]
  have hExp4 : T^(ν+ν*4) ≤ T^ε :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by dsimp only [ν]; linarith)
  have hSourceCut : D₀*(2*T)^ν*(Q:ℝ)^3 ≤ V^4 := by
    have hQ3 : (Q:ℝ)^3 ≤ 8*(M:ℝ)^6 := by
      have hh := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQle 3
      nlinarith only [hh]
    have hd4 : d^4 ≤ B^4*T^(ν*4) := by
      have hp4 := hPow 4
      norm_num only [Nat.cast_ofNat] at hp4
      rw [← hp4]
      exact pow_le_pow_left₀ hd.le hdP 4
    have hL : (D₀*(2*T)^ν*(Q:ℝ)^3)*d^4 ≤ D*T^ε*(M:ℝ)^6 := by
      calc
        _ ≤ (D₀*((2:ℝ)^ν*T^ν)*(8*(M:ℝ)^6))*(B^4*T^(ν*4)) := by
          rw [Real.mul_rpow (by norm_num) hTp.le]
          gcongr
        _ = D*T^(ν+ν*4)*(M:ℝ)^6 := by
          rw [Real.rpow_add hTp]
          dsimp only [D]
          ring_nf
        _ ≤ _ := by gcongr
    dsimp only [V]
    rw [div_pow,← pow_mul,show 2*4=8 by norm_num]
    exact (le_div_iff₀ (pow_pos hd 4)).mpr (hL.trans hCut)
  have hWide : ∀ m ∈ Ioc Q (2*Q), m ∈ Ioc (M^2) (2^2*M^2) := by
    intro m hm
    rw [mem_Ioc] at hm ⊢
    constructor
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left (M^2)
        (pow_pos (by omega) r)) hm.1
    · have hr2 : r+1 ≤ 2 := by have := mem_range.mp hr; omega
      have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hr2
      have heq : 2*Q = 2^(r+1)*M^2 := by dsimp only [Q]; rw [pow_succ]; ring_nf
      rw [heq] at hm
      exact hm.2.trans (Nat.mul_le_mul_right (M^2) hp)
  have hNorm : ∀ m ∈ Ioc Q (2*Q),
      ‖normalizedFinitePoweredCoeffs M 2 a 0 A ν m‖ ≤ 1 := by
    intro m hm
    have hmem := hWide m hm
    exact norm_normalizedFinitePoweredCoeffs_le_one M 2 m a 0 A ν
      hM le_rfl hA hν hmem (hCoeff M a ha m (by
        have := (mem_Ioc.mp hmem).1
        omega))
  have hVeq : (U^2/(A*((2^2*M^2:ℕ):ℝ)^ν))/2 = V := by
    dsimp only [V,d]
    rw [div_div]
    congr 1
    ring_nf
  have hBound := hCount Q (2*T) V (normalizedFinitePoweredCoeffs M 2 a 0 A ν) W'
    hQ (by linarith) (hQle.trans (by linarith)) hV hSourceCut hNorm
    (fun x hx y hy hxy => hSep x (hsub hx) y (hsub hy) hxy)
    (fun x hx => ⟨(hBase x (hsub hx)).1,by have := (hBase x (hsub hx)).2; linarith⟩)
    (by intro t ht; simpa only [Q,Nat.cast_ofNat,hVeq,Real.rpow_zero,one_mul] using hLarge' t ht)
  have hS1 := square_level_monomial_le (Nat.cast_nonneg Q) hMp hTp hU hd hP hQle hdP
    (by norm_num : (0:ℝ)≤2) (by norm_num : (2:ℝ)≤8)
    (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)≤2) (by norm_num : (2:ℝ)≤10)
  have hS2 := square_level_monomial_le (Nat.cast_nonneg Q) hMp hTp hU hd hP hQle hdP
    (by norm_num : (0:ℝ)≤8/3) (by norm_num : (8/3:ℝ)≤8)
    (by norm_num : (0:ℝ)≤2/3) (by norm_num : (2/3:ℝ)≤1)
    (by norm_num : (0:ℝ)≤4) (by norm_num : (4:ℝ)≤10)
  have hS3 := square_level_monomial_le (Nat.cast_nonneg Q) hMp hTp hU hd hP hQle hdP
    (by norm_num : (0:ℝ)≤36/5) (by norm_num : (36/5:ℝ)≤8)
    (by norm_num : (0:ℝ)≤3/5) (by norm_num : (3/5:ℝ)≤1)
    (by norm_num : (0:ℝ)≤48/5) (by norm_num : (48/5:ℝ)≤10)
  norm_num only [Real.rpow_zero,Real.rpow_ofNat,mul_one,
    show (2:ℝ)*2=4 by norm_num,show -(2:ℝ)*2 = -4 by norm_num] at hS1
  norm_num only [show (2:ℝ)*(8/3)=16/3 by norm_num,
    show -(2:ℝ)*4 = -8 by norm_num] at hS2
  norm_num only [show (2:ℝ)*(36/5)=72/5 by norm_num,
    show -(2:ℝ)*(48/5) = -96/5 by norm_num] at hS3
  have hShape : (Q:ℝ)^2*V^(-2:ℝ)+(Q:ℝ)^(8/3:ℝ)*(2*T)^(2/3:ℝ)*V^(-4:ℝ)+
      (Q:ℝ)^(36/5:ℝ)*(2*T)^(3/5:ℝ)*V^(-48/5:ℝ) ≤
      512*(B*T^ν)^10*((M:ℝ)^4*U^(-4:ℝ)+
        T^(2/3:ℝ)*(M:ℝ)^(16/3:ℝ)*U^(-8:ℝ)+
        T^(3/5:ℝ)*(M:ℝ)^(72/5:ℝ)*U^(-96/5:ℝ)) := by
    dsimp only [V]
    nlinarith only [hS1,hS2,hS3]
  have hExp10 : T^(ν+ν*10) ≤ T^ε :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by dsimp only [ν]; linarith)
  calc
    (W.card:ℝ) ≤ 2*(W'.card:ℝ) := by simpa only [Nat.cast_ofNat] using hcard
    _ ≤ 2*(C₀*(2*T)^ν*(512*(B*T^ν)^10*
        ((M:ℝ)^4*U^(-4:ℝ)+T^(2/3:ℝ)*(M:ℝ)^(16/3:ℝ)*U^(-8:ℝ)+
          T^(3/5:ℝ)*(M:ℝ)^(72/5:ℝ)*U^(-96/5:ℝ)))) := by
      exact mul_le_mul_of_nonneg_left (hBound.trans
        (mul_le_mul_of_nonneg_left hShape (by positivity))) (by norm_num)
    _ = C*T^(ν+ν*10)*((M:ℝ)^4*U^(-4:ℝ)+
        T^(2/3:ℝ)*(M:ℝ)^(16/3:ℝ)*U^(-8:ℝ)+
        T^(3/5:ℝ)*(M:ℝ)^(72/5:ℝ)*U^(-96/5:ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hTp.le,hPow,Real.rpow_add hTp]
      dsimp only [C]
      ring_nf
    _ ≤ _ := by gcongr

end Montgomery.RationalMoment
