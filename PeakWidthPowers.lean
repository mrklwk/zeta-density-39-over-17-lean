module
public import GenericPeakClusters

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.CriticalPeak

/-- The first physical width term is exactly sixth-power decay. -/
theorem width_first_term {K P L V H : ℝ}
    (hK : 0 < K) (hP : 0 < P) (hL : 0 < L) (hV : 0 < V) :
    H/((V^2/(K*L^2))*(V^2/(16*P*L))^2) =
      K*(16*P)^2*H*L^4/V^6 := by
  field_simp

/-- Exact height, amplitude and logarithmic powers in the second width term. -/
theorem width_second_term {a g b K P L V H : ℝ}
    (hK : 0 < K) (hP : 0 < P) (hL : 0 < L) (hV : 0 < V) :
    H^a/((V^2/(K*L^2))^g*(V^2/(16*P*L))^b) =
      K^g*(16*P)^b*H^a*L^(2*g+b)/V^(2*g+2*b) := by
  have hVp : V^2 > 0 := sq_pos_of_pos hV
  rw [Real.div_rpow hVp.le (by positivity),
    Real.div_rpow hVp.le (by positivity),
    Real.mul_rpow hK.le (sq_nonneg L),
    Real.mul_rpow (by positivity : 0 ≤ 16*P) hL.le]
  have hLg : (L^2)^g = L^(2*g) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have hVg : (V^2)^g = V^(2*g) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV.le]
    norm_num
  have hVb : (V^2)^b = V^(2*b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV.le]
    norm_num
  rw [hLg,hVg,hVb,Real.rpow_add hL,Real.rpow_add hV]
  have hKg : K^g ≠ 0 := (Real.rpow_pos_of_pos hK _).ne'
  have hLg' : L^(2*g) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have hLb : L^b ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have hPb : (16*P)^b ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  field_simp
end Montgomery.CriticalPeak
