module
public import QuadraticLargeValueBound

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment

/-- Absorption for the actual quadratic inequality. The coefficient of R²
is paid explicitly, rather than dropped as an implicit asymptotic saving. -/
theorem quadratic_scalar_absorption {N L T V R S Q Λ A : ℝ}
    (_hN : 0 < N) (_hL : 0 < L) (_hT : 0 < T) (hV : 0 < V)
    (hS : 0 < S) (hSR : S ≤ R) (hQ : 1 ≤ Q) (hΛ : 1 ≤ Λ) (hA : 0 < A)
    (hquad : R^2*V^4 ≤ A*Λ*((N*L)^2+N^3*R^2+
      (N^3*T/L)*R^((3:ℝ)/2)+N^3*T^((1:ℝ)/4)*R^((19:ℝ)/12)))
    (hsink : 2*A*Λ*N^3 ≤ V^4)
    (hbase : (N*L)^2 ≤ Q*S^2*V^4)
    (hfirst : N^3*T/L ≤ Q*S^((1:ℝ)/2)*V^4)
    (hsecond : N^3*T^((1:ℝ)/4) ≤ Q*S^((5:ℝ)/12)*V^4) :
    R ≤ (1+6*A)^3*Λ^3*Q^3*S := by
  have hR : 0 < R := hS.trans_le hSR
  have hq : 0 < Q := by linarith
  have hl : 0 < Λ := by linarith
  let Y := S^((5:ℝ)/12)*R^((19:ℝ)/12)*V^4
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hb : S^2 ≤ S^((5:ℝ)/12)*R^((19:ℝ)/12) := by
    calc
      _ = S^((5:ℝ)/12)*S^((19:ℝ)/12) := by rw [← Real.rpow_add hS]; norm_num
      _ ≤ _ := by gcongr
  have hf : S^((1:ℝ)/2)*R^((3:ℝ)/2) ≤ S^((5:ℝ)/12)*R^((19:ℝ)/12) := by
    have hs : S^((1:ℝ)/2)=S^((5:ℝ)/12)*S^((1:ℝ)/12) := by rw [← Real.rpow_add hS]; norm_num
    have hr : R^((1:ℝ)/12)*R^((3:ℝ)/2)=R^((19:ℝ)/12) := by rw [← Real.rpow_add hR]; norm_num
    calc
      _ = S^((5:ℝ)/12)*(S^((1:ℝ)/12)*R^((3:ℝ)/2)) := by rw [hs]; ring
      _ ≤ S^((5:ℝ)/12)*(R^((1:ℝ)/12)*R^((3:ℝ)/2)) := by gcongr
      _ = _ := by rw [hr]
  have hb' : (N*L)^2 ≤ Q*Y := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb hq.le) (pow_nonneg hV.le 4)
    exact hbase.trans (hh.trans_eq (by dsimp [Y]; ring))
  have hf' : (N^3*T/L)*R^((3:ℝ)/2) ≤ Q*Y := by
    calc
      _ ≤ (Q*S^((1:ℝ)/2)*V^4)*R^((3:ℝ)/2) := by gcongr
      _ = Q*(S^((1:ℝ)/2)*R^((3:ℝ)/2))*V^4 := by ring
      _ ≤ Q*(S^((5:ℝ)/12)*R^((19:ℝ)/12))*V^4 := by gcongr
      _ = _ := by dsimp [Y]; ring
  have hs' : N^3*T^((1:ℝ)/4)*R^((19:ℝ)/12) ≤ Q*Y := by
    exact (mul_le_mul_of_nonneg_right hsecond (by positivity)).trans_eq (by dsimp [Y]; ring)
  have hsum : (N*L)^2+N^3*R^2+(N^3*T/L)*R^((3:ℝ)/2)+
      N^3*T^((1:ℝ)/4)*R^((19:ℝ)/12) ≤ N^3*R^2+3*Q*Y := by linarith only [hb',hf',hs']
  have hsource := hquad.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hsink' := mul_le_mul_of_nonneg_right hsink (sq_nonneg R)
  have hh : R^2*V^4 ≤ (6*A*Λ*Q)*(S^((5:ℝ)/12)*R^((19:ℝ)/12)*V^4) := by
    dsimp [Y] at hsource
    nlinarith only [hsource,hsink']
  have hpow : R^2=R^((5:ℝ)/12)*R^((19:ℝ)/12) := by rw [← Real.rpow_add hR]; norm_num
  rw [hpow] at hh
  have hh' : R^((5:ℝ)/12) ≤ (6*A*Λ*Q)*S^((5:ℝ)/12) := by
    have he : (R^((5:ℝ)/12))*(R^((19:ℝ)/12)*V^4) ≤
        ((6*A*Λ*Q)*S^((5:ℝ)/12))*(R^((19:ℝ)/12)*V^4) := by nlinarith only [hh]
    exact le_of_mul_le_mul_right he (by positivity)
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ R^((5:ℝ)/12)) hh' (by norm_num : (0:ℝ) ≤ 12/5)
  have hleft : (R^((5:ℝ)/12))^((12:ℝ)/5)=R := by rw [← Real.rpow_mul hR.le]; norm_num
  have hright : ((6*A*Λ*Q)*S^((5:ℝ)/12))^((12:ℝ)/5)=
      (6*A*Λ*Q)^((12:ℝ)/5)*S := by
    rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hS.le]
    norm_num
  rw [hleft,hright] at hp
  let F := (1+6*A)*Λ*Q
  have hF : 1 ≤ F := by
    dsimp [F]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) hΛ) hQ
  have hcoef : (6*A*Λ*Q)^((12:ℝ)/5) ≤ F^3 := by
    calc
      _ ≤ F^((12:ℝ)/5) := Real.rpow_le_rpow (by positivity) (by dsimp [F]; nlinarith) (by norm_num)
      _ ≤ F^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hF (by norm_num)
      _ = _ := Real.rpow_natCast F 3
  exact hp.trans ((mul_le_mul_of_nonneg_right hcoef hS.le).trans_eq (by dsimp [F]; ring))

end Montgomery.RationalMoment
