module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.BetaModelJetEstimates
public import LaterPairs.Native.ExponentPairShiftUniformity

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                          

                                                                          
                                                                           
                                                                         
                                                                         
                                                                        
                                                                         
                                                                          
                                                                 


noncomputable section

open Set Expdb Metric
open scoped ContDiff Topology

namespace TaoTrudgianYang2025.HuxleyModel

                                                                     
                                                                        
                                                                              
def tests (v : Fin 4 → ℝ) : Fin 7 → ℝ :=
  ![v 0, v 1, v 2,
    v 0*v 2-(v 1)^2, v 1*v 3-(v 2)^2,
    3*(v 1)^2-v 0*v 2,
    Matrix.det ![![3*(v 1)^2+4*v 0*v 2,3*v 0*v 1,(v 0)^2],
      ![v 2,v 1,v 0],![v 3,v 2,v 1]]]

theorem tests_monomial (a z x : ℝ) :
    tests ![z*x^3,-a*z*x^2,a*(a+1)*z*x,-a*(a+1)*(a+2)*z] =
      ![z*x^3,-a*z*x^2,a*(a+1)*z*x,
        a*z^2*x^4,a^2*(a+1)*z^2*x^2,
        a*(2*a-1)*z^2*x^4,-a^2*(2*a-1)*z^4*x^8] := by
  funext i
  fin_cases i
  · simp [tests]
  · simp [tests]
  · simp [tests]
  · simp [tests]
    ring
  · simp [tests]
    ring
  · simp [tests]
    ring
  · dsimp [tests]
    erw [Matrix.det_fin_three]
    norm_num
    ring

theorem tests_monomial_ne_zero {a z x : ℝ}
    (ha : 1 < a) (hz : 0 < z) (hx : 0 < x) (i : Fin 7) :
    tests ![z*x^3,-a*z*x^2,a*(a+1)*z*x,-a*(a+1)*(a+2)*z] i ≠ 0 := by
  rw [tests_monomial]
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a+1 := by linarith
  have ha2 : 0 < 2*a-1 := by linarith
  fin_cases i <;> dsimp
  · positivity
  · exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha0.ne') hz.ne')
      (pow_ne_zero _ hx.ne')
  · positivity
  · positivity
  · positivity
  · positivity
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (neg_ne_zero.mpr (pow_ne_zero _ ha0.ne')) ha2.ne') (pow_ne_zero _ hz.ne'))
      (pow_ne_zero _ hx.ne')

theorem continuous_tests (i : Fin 7) : Continuous (fun v => tests v i) := by
  fin_cases i <;> simp [tests] <;> fun_prop

private theorem compact_tests_uniform_lower {n m : ℕ} [Nonempty (Fin m)]
    (f : (Fin n → ℝ) → Fin m → ℝ)
    (hf : ∀ i, Continuous (fun v => f v i))
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hSne : S.Nonempty)
    (hne : ∀ v ∈ S, ∀ i, f v i ≠ 0) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ w ∈ S, ∀ v : Fin n → ℝ, dist v w ≤ δ → ∀ i, c ≤ |f v i| := by
  let U := {v : Fin n → ℝ | ∀ i, f v i ≠ 0}
  have hU : IsOpen U := by
    have hi (i : Fin m) : IsOpen {v : Fin n → ℝ | f v i ≠ 0} :=
      isOpen_ne.preimage (hf i)
    simpa only [Set.iInter_ofPred] using isOpen_iInter_of_finite hi
  obtain ⟨δ,hδ,hδU⟩ := hS.exists_cthickening_subset_open hU hne
  let K := cthickening δ S
  have hK : IsCompact K := hS.cthickening
  have hKne : K.Nonempty := hSne.mono (self_subset_cthickening S)
  have hc : Continuous (fun p : (Fin n → ℝ) × Fin m => |f p.1 p.2|) := by
    apply continuous_abs.comp
    apply continuous_prod_of_discrete_right.mpr
    exact hf
  obtain ⟨p,hp,hmin⟩ := (hK.prod (isCompact_univ : IsCompact (univ : Set (Fin m)))).exists_isMinOn
    (hKne.prod (Set.univ_nonempty)) hc.continuousOn
  refine ⟨δ,|f p.1 p.2|,hδ,abs_pos.mpr (hδU hp.1 p.2),?_⟩
  intro w hw v hv j
  have hvK : v ∈ K := closedBall_subset_cthickening hw δ hv
  exact (isMinOn_iff.mp hmin) (v,j) ⟨hvK,mem_univ j⟩

                                                                          
                                                                              
theorem reference_tests_positive {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) (i : Fin 7) :
    tests (fun j : Fin 4 => iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x) i ≠ 0 := by
  have hj (n : ℕ) : iteratedDeriv n (Expdb.modelPhase σ) x =
      (descPochhammer ℝ n).eval (-σ)*x^(-σ-(n:ℝ)) := by
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const (-σ) x n
  have hp (n : ℕ) (hn : n ≤ 5) :
      x^(-σ-(n:ℝ))=x^(5-n)*x^(-σ-5) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hx]
    congr 1
    rw [Nat.cast_sub hn]
    norm_num
  let z := σ*(σ+1)*x^(-σ-5)
  have he : (fun j : Fin 4 => iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x) =
      ![z*x^3,-(σ+2)*z*x^2,(σ+2)*(σ+3)*z*x,-(σ+2)*(σ+3)*(σ+4)*z] := by
    funext j
    fin_cases j <;> dsimp only [z]
    all_goals
      rw [hj,hp _ (by norm_num)]
      norm_num [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ]
      ring
  rw [he]
  have hh := tests_monomial_ne_zero (a:=σ+2) (z:=z) (x:=x)
    (by linarith only [hσ]) (by dsimp only [z]; positivity) hx i
  simpa only [show σ+2+1=σ+3 by ring,show σ+2+2=σ+4 by ring] using hh

                                                                   
                                                                          
theorem exists_uniform_test_lower_positive_compact
    {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ x ∈ Set.Icc a b, ∀ v : Fin 4 → ℝ,
        (∀ j, |v j-iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x| ≤ δ) →
        ∀ j, c ≤ |tests v j| := by
  let R := fun (x : ℝ) (j : Fin 4) => iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x
  have hR : ContinuousOn R (Set.Icc a b) := by
    apply continuousOn_pi.mpr
    intro j x hx
    exact (contDiffAt_iteratedDeriv_infty
      (Real.contDiffAt_rpow_const_of_ne (ha.trans_le hx.1).ne') (j.val+2)).continuousAt.continuousWithinAt
  let S := R '' Set.Icc a b
  have hS : IsCompact S := isCompact_Icc.image_of_continuousOn hR
  have hSne : S.Nonempty := ⟨R a,a,⟨le_rfl,hab⟩,rfl⟩
  have hn : ∀ v ∈ S, ∀ j, tests v j ≠ 0 := by
    rintro v ⟨x,hx,rfl⟩ j
    exact reference_tests_positive hσ (ha.trans_le hx.1) j
  obtain ⟨δ,c,hδ,hc,hlower⟩ := compact_tests_uniform_lower
    tests continuous_tests hS hSne hn
  refine ⟨δ,c,hδ,hc,?_⟩
  intro x hx v hv
  apply hlower _ (mem_image_of_mem R hx) v
  rw [dist_pi_le_iff hδ.le]
  exact hv

                                                           
                                                                          
def caseTwoTests (w : Fin 7 → ℝ) : Fin 2 → ℝ :=
  ![3*(w 1)^2-w 0*w 2,
    Matrix.det ![![3*(w 1)^2+4*w 0*w 2,3*w 0*w 1,(w 0)^2],
      ![w 3,w 2,w 1],![w 6,w 5,w 4]]]

/-- Retaining the parameter amplitude produces the original seven-test
determinant, with the required row swap and fourth scaling power. -/

theorem caseTwoTests_scaled (v : Fin 4 → ℝ) (y σ : ℝ) :
    caseTwoTests ![-y/σ*v 0,-y/σ*v 1,-y/σ*v 2,-y/σ*v 3,
      -1/σ*v 0,-1/σ*v 1,-1/σ*v 2] =
      ![y^2/σ^2*HuxleyModel.tests v 5,-y^3/σ^4*HuxleyModel.tests v 6] := by
  funext j
  fin_cases j
  · simp [caseTwoTests,HuxleyModel.tests,div_eq_mul_inv]
    ring
  · dsimp [caseTwoTests,HuxleyModel.tests]
    erw [Matrix.det_fin_three, Matrix.det_fin_three]
    norm_num [div_eq_mul_inv]
    ring


theorem continuous_caseTwoTests (j : Fin 2) :
    Continuous (fun w : Fin 7 → ℝ => caseTwoTests w j) := by
  fin_cases j <;> dsimp [caseTwoTests,Matrix.det_fin_three] <;> fun_prop


/-- Uniform robustness of the actual two Case 2 polynomials, before the
original phase or the small shift is selected. -/

theorem caseTwoTests_uniform_stability {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) :
    ∃ ε d : ℝ, 0 < ε ∧ 0 < d ∧
      ∀ (v : Fin 4 → ℝ) (y : ℝ),
      (∀ i, |v i| ≤ U) → c ≤ |HuxleyModel.tests v 5| → c ≤ |HuxleyModel.tests v 6| →
      y ∈ Icc (1:ℝ) 2 → ∀ w : Fin 7 → ℝ,
      (∀ i, |w i- ![-y/σ*v 0,-y/σ*v 1,-y/σ*v 2,-y/σ*v 3,
        -1/σ*v 0,-1/σ*v 1,-1/σ*v 2] i| ≤ ε) →
      ∀ j, d ≤ |caseTwoTests w j| := by
  let A : Set (Fin 4 → ℝ) :=
    (Icc (fun _ => -U) (fun _ => U) ∩ {v | c ≤ |HuxleyModel.tests v 5|}) ∩
      {v | c ≤ |HuxleyModel.tests v 6|}
  have hA : IsCompact A :=
    (isCompact_Icc.inter_right
      (isClosed_le continuous_const (HuxleyModel.continuous_tests 5).abs)).inter_right
        (isClosed_le continuous_const (HuxleyModel.continuous_tests 6).abs)
  let ψ := fun p : (Fin 4 → ℝ) × ℝ =>
    ![-p.2/σ*p.1 0,-p.2/σ*p.1 1,-p.2/σ*p.1 2,-p.2/σ*p.1 3,
      -1/σ*p.1 0,-1/σ*p.1 1,-1/σ*p.1 2]
  have hψ : Continuous ψ := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp only [ψ] <;> fun_prop
  let S := ψ '' (A ×ˢ Icc (1:ℝ) 2)
  have hS : IsCompact S := (hA.prod isCompact_Icc).image hψ
  have hmem (v : Fin 4 → ℝ) y (hv : ∀ i, |v i| ≤ U)
      (h₅ : c ≤ |HuxleyModel.tests v 5|) (h₆ : c ≤ |HuxleyModel.tests v 6|)
      (hy : y ∈ Icc (1:ℝ) 2) : ψ (v,y) ∈ S := by
    apply mem_image_of_mem
    exact ⟨⟨⟨⟨fun i => (abs_le.mp (hv i)).1,fun i => (abs_le.mp (hv i)).2⟩,h₅⟩,h₆⟩,hy⟩
  by_cases hSne : S.Nonempty
  · have hn : ∀ w ∈ S, ∀ j, caseTwoTests w j ≠ 0 := by
      rintro w ⟨⟨v,y⟩,⟨hv,hy⟩,rfl⟩ j
      have hy0 : 0 < y := zero_lt_one.trans_le hy.1
      have hn₅ := abs_pos.mp (hc.trans_le hv.1.2)
      have hn₆ := abs_pos.mp (hc.trans_le hv.2)
      change caseTwoTests ![-y/σ*v 0,-y/σ*v 1,-y/σ*v 2,-y/σ*v 3,
        -1/σ*v 0,-1/σ*v 1,-1/σ*v 2] j ≠ 0
      rw [caseTwoTests_scaled]
      fin_cases j
      · exact mul_ne_zero (div_ne_zero (pow_ne_zero 2 hy0.ne') (pow_ne_zero 2 hσ.ne')) hn₅
      · exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 hy0.ne'))
          (pow_ne_zero 4 hσ.ne')) hn₆
    obtain ⟨ε,d,hε,hd,hstab⟩ := compact_tests_uniform_lower
      caseTwoTests continuous_caseTwoTests hS hSne hn
    refine ⟨ε,d,hε,hd,?_⟩
    intro v y hv h₅ h₆ hy w hw j
    apply hstab _ (hmem v y hv h₅ h₆ hy) w ?_ j
    rw [dist_pi_le_iff hε.le]
    exact hw
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro v y hv h₅ h₆ hy
    exfalso
    exact hSne ⟨_,hmem v y hv h₅ h₆ hy⟩

end TaoTrudgianYang2025.HuxleyModel
