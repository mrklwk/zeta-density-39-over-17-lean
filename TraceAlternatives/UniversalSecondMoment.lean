module
public import TraceAlternatives.UniversalSecondMomentLog

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

theorem universalShortProfile_double {T M R E : ℝ}
    (hT : 0≤T) (hM : 0≤M) (hR : 0≤R) (hE : 0≤E) :
    universalShortProfile (2*T) M R E ≤ 2*universalShortProfile T M R E := by
  have h2a : (2*T)^(1/6:ℝ) ≤ 2*T^(1/6:ℝ) := by
    rw [Real.mul_rpow (by norm_num) hT]
    exact mul_le_mul_of_nonneg_right (by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
        (by norm_num : (1/6:ℝ)≤1)
      simpa only [Real.rpow_one] using hh) (by positivity)
  have h2b : (2*T)^(1/16:ℝ) ≤ 2*T^(1/16:ℝ) := by
    rw [Real.mul_rpow (by norm_num) hT]
    exact mul_le_mul_of_nonneg_right (by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
        (by norm_num : (1/16:ℝ)≤1)
      simpa only [Real.rpow_one] using hh) (by positivity)
  have ha := mul_le_mul_of_nonneg_right h2a
    (by positivity : (0:ℝ)≤M^(4/3:ℝ)*R*E^(1/4:ℝ))
  have hb := mul_le_mul_of_nonneg_right h2b
    (by positivity : (0:ℝ)≤M^(3/2:ℝ)*R^(19/12:ℝ)*E^(5/48:ℝ))
  unfold universalShortProfile universalShortSublinearProfile
  nlinarith only [ha,hb,mul_nonneg (Real.rpow_nonneg hM (3/2)) (sq_nonneg R),
    mul_nonneg (sq_nonneg M) (Real.rpow_nonneg hE (1/2))]

/-- Unconditional universal quadratic short-S2 alternative, with all losses
absorbed into an arbitrary positive height power and the low-level R² term
retained. Actual unit coefficients and the original ordered energy are used. -/
theorem actual_second_moment_universal_native (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (M : ℕ) (T : ℝ) (a : ℕ→ℂ) (W : Finset ℝ),
      0<M → 2≤T → (M:ℝ)^2≤T →
      (∀ n∈Ioc M (2*M), ‖a n‖≤1) → InBaseInterval T W →
      (∑ t∈W, ∑ u∈W, ‖dirichletPoly M a (t-u)‖^2) ≤
      C*T^ε*universalShortProfile T M W.card (discreteAdditiveEnergy W) := by
  let δ : ℝ := ε/2
  have hδ : 0<δ := by dsimp only [δ]; positivity
  obtain ⟨K,hK,hS2⟩ := actual_second_moment_universal_log δ hδ
  let A : ℝ := 1+8*K*(2:ℝ)^δ
  let L : ℝ := 2+1/(δ*Real.log 2)
  have hLog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0<A := by dsimp only [A]; positivity
  have hL : 0<L := by dsimp only [L]; positivity
  refine ⟨A*L,mul_pos hA hL,?_⟩
  intro M T a W hM hT hMT ha hBase
  have hTp : 0<T := by linarith
  have hT1 : 1≤T := by linarith
  have hM1 : (1:ℝ)≤M := by exact_mod_cast hM
  have hTδ : 1≤T^δ := Real.one_le_rpow hT1 hδ.le
  let F : ℝ := universalShortProfile T M W.card (discreteAdditiveEnergy W)
  have hF : 0≤F := universalShortProfile_nonneg hTp.le
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hR : (W.card:ℝ)^2≤F := by
    have hh := Real.one_le_rpow hM1 (by norm_num : (0:ℝ)≤3/2)
    have hSub := universalShortSublinearProfile_nonneg hTp.le
      (Nat.cast_nonneg M) (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
    dsimp only [F,universalShortProfile]
    nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg (W.card:ℝ)),hSub]
  have hInner : (W.card:ℝ)^2+4*K*(2*T)^δ*
      universalShortProfile (2*T) M W.card (discreteAdditiveEnergy W) ≤ A*T^δ*F := by
    have hDouble := universalShortProfile_double hTp.le (Nat.cast_nonneg M)
      (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
    calc
      _ ≤ F+4*K*((2:ℝ)^δ*T^δ)*(2*F) := by
        rw [Real.mul_rpow (by norm_num) hTp.le]
        gcongr
      _ ≤ T^δ*F+4*K*((2:ℝ)^δ*T^δ)*(2*F) := by gcongr; exact le_mul_of_one_le_left hF hTδ
      _ = _ := by dsimp only [A]; ring
  have hLog : 2+Real.logb 2 T ≤ L*T^δ := by
    have hh := Real.log_le_rpow_div hTp.le hδ
    have hDiv := div_le_div_of_nonneg_right hh hLog2.le
    unfold Real.logb
    calc
      _ ≤ 2*T^δ+(T^δ/δ)/Real.log 2 := add_le_add (by nlinarith) hDiv
      _ = _ := by dsimp only [L]; field_simp
  have hInner0 : 0≤(W.card:ℝ)^2+4*K*(2*T)^δ*
      universalShortProfile (2*T) M W.card (discreteAdditiveEnergy W) := by
    have hh := universalShortProfile_nonneg (by positivity : (0:ℝ)≤2*T)
      (Nat.cast_nonneg M) (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
    positivity
  have hBound := hS2 M T a W hM hT hMT ha hBase
  calc
    _ ≤ (L*T^δ)*(A*T^δ*F) := hBound.trans (mul_le_mul hLog hInner
      hInner0 (by positivity))
    _ = (A*L)*T^ε*F := by
      rw [show (L*T^δ)*(A*T^δ*F) = (A*L)*(T^δ*T^δ)*F by ring,
        ← Real.rpow_add hTp,show δ+δ=ε by dsimp only [δ]; ring]

end Montgomery.RationalMoment
