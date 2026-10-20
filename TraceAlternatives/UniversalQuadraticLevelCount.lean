module
public import QuadraticLargeValueBound
public import GuthMaynard.Improvement.SeparatedSecondMoment
public import DensityEnergyGM.PolynomialHeightSecondEnergy
public import DensityEnergyGM.LargeValuesFinal

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement GuthMaynard.NativeMoment

/-- The actual separated classical mean square, uniformly on every real
source scale between one and the physical height. -/
theorem universal_quadratic_classical_mass (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ T t₀ N : ℝ, 2 ≤ T → 1 ≤ N → N ≤ T →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ∀ V : ℝ, 0 ≤ V → (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ)*V^2 ≤ K*T^η*T*N := by
  let H : ℝ := 1+(2:ℝ)^η/η
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨12+48*H,by positivity,?_⟩
  intro T t₀ N hT hN hNT a ha W hW hsep V hV hlarge
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by linarith
  have ht : 1 ≤ T^η := Real.one_le_rpow (by linarith) hη.le
  have hlog : 1+Real.log ⌊2*N⌋₊ ≤ H*T^η := by
    simpa only [div_one, H,Real.rpow_one] using
      polynomial_height_log_loss 1 η (by norm_num) hη (by linarith) hNp
        (by simpa using hNT)
  have hf : (⌊2*N⌋₊:ℝ) ≤ 2*T := (Nat.floor_le (by positivity : 0 ≤ 2*N)).trans (by linarith)
  have hraw := separated_second_moment_raw hNp (by linarith : 0 ≤ T) a
    (by simpa only [sourceRatioIndices,amplifierSource] using ha) W hW hsep
  have hsum : (W.card:ℝ)*V^2 ≤ ∑ t∈W,‖boundedPolynomial N a t‖^2 := by
    calc
      _ = ∑ _t∈W,V^2 := by simp
      _ ≤ _ := sum_le_sum (fun t ht => pow_le_pow_left₀ hV (hlarge t ht) 2)
  apply hsum.trans (hraw.trans ?_)
  calc
    _ ≤ 3*((2*T)+4*(2*T)*(H*T^η))*(2*N) := by gcongr <;> linarith
    _ = 12*T*N+48*H*T^η*T*N := by ring_nf
    _ ≤ (12+48*H)*T^η*T*N := by
      have hh := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ 12*T*N)
      nlinarith only [hh]

/-- Exact real monomial root bookkeeping for the two amplifier alternatives. -/
theorem universal_quadratic_monomial_root {K N T V : ℝ}
    (δ α β b q : ℝ) (hK : 0 ≤ K) (hN : 0 ≤ N) (hT : 0 ≤ T) (hV : 0 ≤ V) :
    (K*T^δ*N^α*T^β/V^b)^q =
      K^q*T^(δ*q)*N^(α*q)*T^(β*q)*V^(-b*q) := by
  rw [Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hK (by positivity),
    ←Real.rpow_mul hT,←Real.rpow_mul hN,←Real.rpow_mul hT,←Real.rpow_mul hV,
    div_eq_mul_inv,←Real.rpow_neg hV]
  congr 1
  ring_nf

/-- A coefficient-uniform actual level count, above an explicit arbitrarily
small power loss in the natural three-quarter amplitude cutoff. The classical
mean square supplies the upper amplifier-length restriction internally. -/
theorem universal_quadratic_level_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ T t₀ N V : ℝ,
      2 ≤ T → 1 ≤ N → N ≤ T → 0 < V → D*T^ε*N^3 ≤ V^4 →
      ∀ a : ℕ → ℂ, (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*T^ε*(N^2*V^(-2:ℝ)+
        N^(8/3:ℝ)*T^(2/3:ℝ)*V^(-4:ℝ)+
        N^(36/5:ℝ)*T^(3/5:ℝ)*V^(-48/5:ℝ)) := by
  let η : ℝ := ε/3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Q,hQ,hquad⟩ := finite_quadratic_large_value_second MathCollab.Density.comparisonCutoff hη
  obtain ⟨K,hK,hmass⟩ := universal_quadratic_classical_mass η hη
  let A : ℝ := K+8*Q+8
  let B : ℝ := (4*Q*A)^(2/3:ℝ)
  let F : ℝ := (4*Q)^(12/5:ℝ)
  let C : ℝ := A+B+F+1
  let D : ℝ := 8*Q+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hAK : K ≤ A := by dsimp [A]; linarith
  have hA8 : 8*Q ≤ A^2 := by
    have ha : 8*Q ≤ A := by dsimp [A]; linarith
    nlinarith [sq_nonneg (A-1)]
  have hB : 0 < B := by dsimp [B]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,D,hC,by dsimp [D]; positivity,?_⟩
  intro T t₀ N V hT hN hNT hV hcut a ha W hW hsep hlarge
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by linarith
  have ht : 1 ≤ T^η := Real.one_le_rpow (by linarith) hη.le
  have hpow : T^η ≤ T^ε := Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [η]; linarith)
  have hpow1 : T^(4*η/3) ≤ T^ε := Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [η]; linarith)
  have hpow2 : T^(12*η/5) ≤ T^ε := Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [η]; linarith)
  let R : ℝ := W.card
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  by_cases hR : 0 < R
  swap
  · have he : R=0 := by linarith
    change R ≤ _
    rw [he]
    positivity
  let L : ℝ := R*V^2/(A*T^η*N)
  have hLp : 0 < L := by dsimp [L]; positivity
  have hm : R*V^2 ≤ K*T^η*T*N := hmass T t₀ N hT hN hNT a ha W hW hsep V hV.le hlarge
  have hLT : L ≤ T := by
    apply (div_le_iff₀ (by positivity : 0 < A*T^η*N)).mpr
    exact hm.trans (by
      calc
        K*T^η*T*N ≤ A*T^η*T*N := by gcongr
        _ = T*(A*T^η*N) := by ring_nf)
  let Z : ℝ := N^2*V^(-2:ℝ)+N^(8/3:ℝ)*T^(2/3:ℝ)*V^(-4:ℝ)+
    N^(36/5:ℝ)*T^(3/5:ℝ)*V^(-48/5:ℝ)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  by_cases hNL : N ≤ L
  swap
  · have hs : R*V^2 ≤ A*T^η*N^2 := by
      have hh := (div_lt_iff₀ (by positivity : 0 < A*T^η*N)).mp (lt_of_not_ge hNL)
      nlinarith
    have hr : R ≤ A*T^η*(N^2*V^(-2:ℝ)) := by
      have hh := (le_div_iff₀ (sq_pos_of_pos hV)).mpr hs
      rw [Real.rpow_neg hV.le, Real.rpow_two]
      simpa only [div_eq_mul_inv,mul_assoc] using hh
    change R ≤ C*T^ε*Z
    apply hr.trans
    calc
      _ ≤ C*T^ε*(N^2*V^(-2:ℝ)) := by gcongr; dsimp [C]; linarith
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        dsimp [Z]
        linarith [show 0≤N^(8/3:ℝ)*T^(2/3:ℝ)*V^(-4:ℝ) by positivity,
          show 0≤N^(36/5:ℝ)*T^(3/5:ℝ)*V^(-48/5:ℝ) by positivity]
  have hq := hquad T t₀ N L (by linarith) hN hNL hLT a ha W V hV.le hW hlarge hsep
  change R^2*V^4 ≤ Q*T^η*((N*L)^2+N^3*R^2+(N^3*T/L)*R^(3/2:ℝ)+N^3*T^(1/4:ℝ)*R^(19/12:ℝ)) at hq
  have hbase : 8*(Q*T^η*(N*L)^2) ≤ R^2*V^4 := by
    have hEq : (A*T^η)^2*(N*L)^2=R^2*V^4 := by dsimp [L]; field_simp
    have hh : 8*Q*T^η ≤ (A*T^η)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hA8) (Real.rpow_nonneg hTp.le η),mul_nonneg (sq_nonneg A) (mul_nonneg (Real.rpow_nonneg hTp.le η) (sub_nonneg.mpr ht))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg (N*L))]
  have hdiag : 8*(Q*T^η*N^3*R^2) ≤ R^2*V^4 := by
    have hs : 8*Q*T^η*N^3 ≤ V^4 := by
      apply le_trans _ hcut
      dsimp [D]
      nlinarith [mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ 8*Q*N^3),mul_nonneg (Real.rpow_nonneg hTp.le ε) (pow_nonneg hNp.le 3)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg R)]
  have hrest : R^2*V^4 ≤ 2*Q*T^η*((N^3*T/L)*R^(3/2:ℝ)+N^3*T^(1/4:ℝ)*R^(19/12:ℝ)) := by
    have hp : 0 ≤ R^2*V^4 := by positivity
    nlinarith only [hq,hbase,hdiag,hp]
  have hor : R^2*V^4 ≤ 4*Q*T^η*(N^3*T/L)*R^(3/2:ℝ) ∨
      R^2*V^4 ≤ 4*Q*T^η*N^3*T^(1/4:ℝ)*R^(19/12:ℝ) := by
    by_contra hn
    push Not at hn
    nlinarith only [hrest,hn.1,hn.2]
  rcases hor with hfirst | hsecond
  · have hId : 4*Q*T^η*(N^3*T/L)*R^(3/2:ℝ) =
        (4*Q*A)*T^(2*η)*N^4*T/V^2*R^(1/2:ℝ) := by
      have hp : R^(3/2:ℝ)=R*R^(1/2:ℝ) := by
        calc
          _ = R^(1+1/2:ℝ) := by norm_num
          _ = R^((1:ℝ))*R^(1/2:ℝ) := Real.rpow_add hR _ _
          _ = _ := by rw [Real.rpow_one]
      rw [hp,show T^(2*η)=T^η*T^η by rw [←Real.rpow_add hTp];congr 1;ring_nf]
      dsimp [L]
      field_simp
    rw [hId] at hfirst
    have hb := gm_solve_monomial hR (by positivity : 0<V^4) (by norm_num : 0<(2:ℝ)-1/2)
      (p:=2) (q:=1/2) (A:=(4*Q*A)*T^(2*η)*N^4*T/V^2) (E:=1) (by
        simpa only [Real.rpow_two,mul_one] using hfirst)
    norm_num only [show (1:ℝ)/(2-1/2)=2/3 by norm_num, mul_one] at hb
    have he : ((4*Q*A)*T^(2*η)*N^4*T/V^2/V^4)^(2/3:ℝ) =
        B*T^(4*η/3)*(N^(8/3:ℝ)*T^(2/3:ℝ)*V^(-4:ℝ)) := by
      have hv : (4*Q*A)*T^(2*η)*N^4*T/V^2/V^4 = (4*Q*A)*T^(2*η)*N^4*T/V^(6:ℝ) := by norm_num [Real.rpow_ofNat];field_simp
      rw [hv]
      have hh := universal_quadratic_monomial_root (2*η) 4 1 6 (2/3) (by positivity : 0≤4*Q*A) hNp.le hTp.le hV.le
      norm_num only [Real.rpow_ofNat,Real.rpow_one,show (2*η)*(2/3)=4*η/3 by ring_nf] at hh
      convert hh using 1 <;> norm_num [B]; ring_nf
    change R ≤ C*T^ε*Z
    apply (hb.trans_eq he).trans
    calc
      _ ≤ C*T^ε*(N^(8/3:ℝ)*T^(2/3:ℝ)*V^(-4:ℝ)) := by gcongr; dsimp [C]; linarith
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        dsimp [Z]
        linarith [show 0≤N^2*V^(-2:ℝ) by positivity,
          show 0≤N^(8/3:ℝ)*T^(2/3:ℝ)*V^(-4:ℝ) by positivity,
          show 0≤N^(36/5:ℝ)*T^(3/5:ℝ)*V^(-48/5:ℝ) by positivity]
  · have hb := gm_solve_monomial hR (by positivity : 0<V^4) (by norm_num : 0<(2:ℝ)-19/12)
      (p:=2) (q:=19/12) (A:=4*Q*T^η*N^3*T^(1/4:ℝ)) (E:=1) (by
        simpa only [Real.rpow_two,mul_one] using hsecond)
    norm_num only [show (1:ℝ)/(2-19/12)=12/5 by norm_num, mul_one] at hb
    have he : (4*Q*T^η*N^3*T^(1/4:ℝ)/V^4)^(12/5:ℝ) =
        F*T^(12*η/5)*(N^(36/5:ℝ)*T^(3/5:ℝ)*V^(-48/5:ℝ)) := by
      have hh := universal_quadratic_monomial_root η 3 (1/4) 4 (12/5) (by positivity : 0≤4*Q) hNp.le hTp.le hV.le
      norm_num only [Real.rpow_ofNat,show η*(12/5)=12*η/5 by ring_nf] at hh
      convert hh using 1; norm_num [F]; ring_nf
    change R ≤ C*T^ε*Z
    apply (hb.trans_eq he).trans
    calc
      _ ≤ C*T^ε*(N^(36/5:ℝ)*T^(3/5:ℝ)*V^(-48/5:ℝ)) := by gcongr; dsimp [C]; linarith
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        dsimp [Z]
        linarith [show 0≤N^2*V^(-2:ℝ) by positivity,
          show 0≤N^(8/3:ℝ)*T^(2/3:ℝ)*V^(-4:ℝ) by positivity,
          show 0≤N^(36/5:ℝ)*T^(3/5:ℝ)*V^(-48/5:ℝ) by positivity]

end Montgomery.RationalMoment
