import GuthMaynard.Improvement.MiddleMomentRaw
import GuthMaynard.Improvement.RemovedMassBound
import GuthMaynard.Improvement.MomentScalarClosure
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual truncated fourth moment in the full middle range. No analytic
estimate remains a premise; the constant precedes the source and both scales. -/
theorem middle_fourth_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T : ℝ, 2 ≤ N →
      N^((6:ℝ)/5) ≤ T → T ≤ N^((5:ℝ)/3) →
      ∀ a : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∫ t, (sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T))
        (boundedPolynomial N a) (middleThreshold N T) t)^2) ≤
        C*N^ε*middleMoment N T := by
  let θ := ε/6
  have hθ : 0 < θ := by dsimp [θ]; positivity
  obtain ⟨S,C,D,hS,hC,hD,hr⟩ := middle_source_moment_raw hθ hθ
  obtain ⟨K,hK,hremoved⟩ := fixed_source_removed_mass hθ
  let J := Real.log 2+1/θ
  have hJ : 0 < J := by dsimp [J]; positivity
  let Q := S*(150+C*(5:ℝ)^θ*(5+5*D*(1+2*K)+3060*D*J^2))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨1+3*Q,by positivity,?_⟩
  intro N T hN hlo hhi a ha
  obtain ⟨hNT,hTN⟩ := middle_time_bounds hN hlo hhi
  obtain ⟨hNL,_,_⟩ := middle_length_bounds hN hlo hhi
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have hn1 : 1 ≤ N := by linarith
  have ht1 : 1 ≤ T := by linarith
  let L := middleLength N T
  let U := middleThreshold N T
  let P := middleMoment N T
  let μ := sourceTruncatedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U
  let H := ∫ t, sourceRemovedDensity (fun t => fixedTimeCutoff (t/T)) (boundedPolynomial N a) U t
  let M := ∫ t, μ t^2
  have hP : 0 ≤ P := by dsimp [P,middleMoment]; positivity
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  have hH0 : 0 ≤ H := by
    apply integral_nonneg
    intro t
    exact indicator_nonneg (fun x _ => mul_nonneg (fixedTimeCutoff_bounds (x/T)).1 (sq_nonneg _)) t
  have hU : 1 ≤ U := middle_threshold_ge_one hn1 ht1
  have hrem := hremoved N T U hN hNT hTN hU a ha
  have hu4 : T*N^4/U^4=N*L := middle_threshold_fourth_quotient hn ht
  rw [hu4] at hrem
  have hH : H ≤ (2*K)*N^θ*N*L := by
    have hN2 : N^2 ≤ N*L := by nlinarith [mul_le_mul_of_nonneg_left hNL hn.le]
    calc
      _ ≤ K*N^θ*(N^2+N*L) := hrem
      _ ≤ K*N^θ*(2*N*L) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hR : (5*T)^θ ≤ (5:ℝ)^θ*N^(2*θ) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤5) ht.le]
    have hh := Real.rpow_le_rpow ht.le hTN hθ.le
    rw [← Real.rpow_natCast N 2,← Real.rpow_mul hn.le] at hh
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hlog0 : 0 ≤ Real.log (2*N) := Real.log_nonneg (by linarith)
  have hlog : (Real.log (2*N))^2 ≤ J^2*N^(2*θ) := by
    have hh := pow_le_pow_left₀ hlog0 (classical_log_budget hn1 hθ) 2
    calc
      _ ≤ (J*N^θ)^2 := hh
      _ = _ := by
        rw [mul_pow,← Real.rpow_natCast (N^θ) 2,← Real.rpow_mul hn.le]
        congr 2
        ring
  have hX : 1 ≤ N^θ := Real.one_le_rpow hn1 hθ.le
  have hY : 1 ≤ N^(2*θ) := Real.one_le_rpow hn1 (by positivity)
  have hb := raw_moment_normalized_budget hn.le hNL ht.le hP hM hS.le hC.le hD.le
    (show 0 ≤ 2*K by positivity) (show 0 ≤ (5:ℝ)^θ by positivity)
    (show 0 ≤ J^2 by positivity) (Real.rpow_nonneg hn.le θ) hX hY hY hH0 hH hR hlog
    (middle_length_moment_square hn ht) (middle_cubic_budget hn ht hhi)
    (hr N T hN hlo hhi a ha)
  have he : N^θ*N^θ*N^(2*θ)*N^(2*θ)=N^ε := by
    rw [← Real.rpow_add hn,← Real.rpow_add hn,← Real.rpow_add hn]
    congr 1
    dsimp [θ]
    ring
  have hnorm : M^3 ≤ Q*N^ε*(P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M) := by
    change M^3 ≤ Q*N^θ*N^θ*N^(2*θ)*N^(2*θ)*
      (P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M) at hb
    calc
      _ ≤ Q*N^θ*N^θ*N^(2*θ)*N^(2*θ)*(P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M) := hb
      _ = Q*(N^θ*N^θ*N^(2*θ)*N^(2*θ))*(P^3+P*Real.sqrt P*M*Real.sqrt M+P^2*M) := by ring
      _ = _ := by rw [he]
  exact normalized_moment_power_absorption hM hP hQ hn1 hε.le hnorm

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.middle_fourth_moment
