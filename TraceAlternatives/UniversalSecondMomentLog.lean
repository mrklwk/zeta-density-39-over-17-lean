module
public import TraceAlternatives.UniversalDifferenceLevels
public import TraceAlternatives.UniversalWeakProfile
public import TraceAlternatives.DyadicWeakMoment

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

def universalShortProfile (T M R E : ℝ) : ℝ :=
  M^(3/2:ℝ)*R^2+universalShortSublinearProfile T M R E

theorem universalShortProfile_nonneg {T M R E : ℝ}
    (hT : 0≤T) (hM : 0≤M) (hR : 0≤R) (hE : 0≤E) :
    0≤universalShortProfile T M R E := by
  exact add_nonneg (by positivity) (universalShortSublinearProfile_nonneg hT hM hR hE)

/-- The complementary small-amplitude range is bounded without discarding
its quadratic cardinality factor. -/
theorem universal_low_level_bound {D H M U δ : ℝ}
    (hD : 0≤D) (hH : 1≤H) (hM : 0≤M) (hU : 0≤U) (hδ : 0≤δ)
    (hCut : U^8 ≤ D*H^δ*M^6) :
    U^2 ≤ (1+D)*H^δ*M^(3/2:ℝ) := by
  have hHp : 0 < H := by linarith
  have hh := Real.rpow_le_rpow (pow_nonneg hU 8) hCut (by norm_num : (0:ℝ)≤1/4)
  have hLeft : (U^8)^(1/4:ℝ)=U^2 := by
    rw [← Real.rpow_natCast_mul hU]
    norm_num [Real.rpow_ofNat]
  have hRight : (D*H^δ*M^6)^(1/4:ℝ)=D^(1/4:ℝ)*H^(δ/4)*M^(3/2:ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow hD (by positivity),
      ← Real.rpow_mul hHp.le,← Real.rpow_natCast_mul hM]
    norm_num only [Nat.cast_ofNat, show (6:ℝ)*(1/4)=3/2 by norm_num]
    rw [show δ*(1/4:ℝ)=δ/4 by ring]
  rw [hLeft,hRight] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (fractional_constant_le_one_add hD (by norm_num) (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le hH (by linarith)) (by positivity) (by positivity))
    (by positivity))

/-- Actual short second moment, retaining the precise logarithmic factor.
No separation of the original ordinates is required. -/
theorem actual_second_moment_universal_log (δ : ℝ) (hδ : 0<δ) :
    ∃ K : ℝ, 0<K ∧ ∀ (M : ℕ) (T : ℝ) (a : ℕ→ℂ) (W : Finset ℝ),
      0<M → 2≤T → (M:ℝ)^2≤T →
      (∀ n∈Ioc M (2*M), ‖a n‖≤1) → InBaseInterval T W →
      (∑ t∈W, ∑ u∈W, ‖dirichletPoly M a (t-u)‖^2) ≤
      (2+Real.logb 2 T)*((W.card:ℝ)^2+4*K*(2*T)^δ*
        universalShortProfile (2*T) M W.card (discreteAdditiveEnergy W)) := by
  classical
  obtain ⟨C,D,hC,hD,hLevels⟩ := universal_difference_cell_level_count δ hδ
  let K : ℝ := 2+D+3*C
  have hK : 0<K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro M T a W hM hT hMT ha hBase
  have hTp : 0<T := by linarith
  have hH : 1≤2*T := by linarith
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  obtain ⟨p,hrep,hCount⟩ := hLevels M T a W hM hT hMT ha hBase
  let S := differenceFloorSupport W
  let r : ℤ→ℝ := fun j => differenceFloorCount W j
  let v : ℤ→ℝ := fun j => ‖dirichletPoly M a ((p j).1-(p j).2)‖
  have hr : ∀ j∈S, 0≤r j := fun _ _ => Nat.cast_nonneg _
  have hv : ∀ j∈S, 0≤v j := fun _ _ => norm_nonneg _
  have hTotal : (∑ j∈S, r j) = (W.card:ℝ)^2 := by
    dsimp only [S,r]
    exact_mod_cast sum_differenceFloorCount W
  have hvM : ∀ j∈S, v j≤M := by
    intro j hj
    dsimp only [v]
    exact norm_negative_polynomial_le_scale a _ ha
  have hvT : ∀ j∈S, v j≤T := by
    intro j hj
    have hM1 : (1:ℝ)≤M := by exact_mod_cast hM
    have hm : (M:ℝ)≤T := by nlinarith
    exact (hvM j hj).trans hm
  let F := universalShortProfile (2*T) M W.card (discreteAdditiveEnergy W)
  have hF : 0≤F := universalShortProfile_nonneg (by positivity)
    hMp.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hWeak : ∀ U : ℝ, 1≤U →
      U^2*(∑ j∈S.filter (fun j => U≤v j), r j) ≤ K*(2*T)^δ*F := by
    intro U hU1
    have hU : 0<U := by linarith
    let J := S.filter (fun j => U≤v j)
    let mass : ℝ := ∑ j∈J, r j
    have hmass : 0 ≤ mass := sum_nonneg (fun j hj => Nat.cast_nonneg _)
    have hmassR : mass≤(W.card:ℝ)^2 := by
      rw [← hTotal]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun j hj hn => Nat.cast_nonneg _)
    have hSub : 0≤universalShortSublinearProfile (2*T) M W.card (discreteAdditiveEnergy W) :=
      universalShortSublinearProfile_nonneg (by positivity) hMp.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    by_cases hCut : D*(2*T)^δ*(M:ℝ)^6 ≤ U^8
    · have hJ := hCount U hU hCut
      have hSq := differenceFloor_subset_mass_sq W J (filter_subset _ _)
      have hSq' : mass^2 ≤ (discreteAdditiveEnergy W:ℝ)*(C*(2*T)^δ)*
          ((M:ℝ)^4*U^(-4:ℝ)+(2*T)^(2/3:ℝ)*(M:ℝ)^(16/3:ℝ)*U^(-8:ℝ)+
          (2*T)^(3/5:ℝ)*(M:ℝ)^(72/5:ℝ)*U^(-96/5:ℝ)) := by
        have hh := mul_le_mul_of_nonneg_right hJ (Nat.cast_nonneg (discreteAdditiveEnergy W): (0:ℝ)≤_)
        dsimp only [mass,r,J,S,v] at *
        nlinarith only [hSq,hh]
      have hh := universal_weak_level_profile (by positivity : (0:ℝ)≤2*T)
        hMp.le (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
        (by positivity : (0:ℝ)≤C*(2*T)^δ) hU hmass hmassR hSq'
      have hCoeff : 1+3*(C*(2*T)^δ) ≤ K*(2*T)^δ := by
        have hh := Real.one_le_rpow hH hδ.le
        dsimp only [K]
        nlinarith only [hh,mul_nonneg hD.le (Real.rpow_nonneg (by positivity : (0:ℝ)≤2*T) δ)]
      exact hh.trans ((mul_le_mul_of_nonneg_right hCoeff hSub).trans
        (mul_le_mul_of_nonneg_left (by dsimp only [F,universalShortProfile]; exact le_add_of_nonneg_left (by positivity) :
          universalShortSublinearProfile (2*T) M W.card (discreteAdditiveEnergy W)≤F) (by positivity)))
    · have hLow := universal_low_level_bound hD.le hH hMp.le hU.le hδ.le (le_of_not_ge hCut)
      have hKR : (1+D)≤K := by dsimp only [K]; linarith
      calc
        _ ≤ ((1+D)*(2*T)^δ*(M:ℝ)^(3/2:ℝ))*(W.card:ℝ)^2 :=
          mul_le_mul hLow hmassR hmass (by positivity)
        _ ≤ K*(2*T)^δ*((M:ℝ)^(3/2:ℝ)*(W.card:ℝ)^2) := by
          nlinarith only [mul_le_mul_of_nonneg_right hKR
            (by positivity : (0:ℝ)≤(2*T)^δ*(M:ℝ)^(3/2:ℝ)*(W.card:ℝ)^2)]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          dsimp only [F,universalShortProfile]
          linarith
  have hDyad := finite_dyadic_weighted_square_bound S r v hT
    (by positivity : 0≤K*(2*T)^δ*F) hr hv hvT hWeak
  rw [hTotal] at hDyad
  have hOriginal : (∑ t∈W, ∑ u∈W, ‖dirichletPoly M a (t-u)‖^2) ≤
      ∑ j∈S, r j*v j^2 := by
    calc
      _ = ∑ q∈differenceOrdinatePairs W, ‖dirichletPoly M a (q.1-q.2)‖^2 := by
        rw [differenceOrdinatePairs,sum_product]
      _ ≤ ∑ q∈differenceOrdinatePairs W, v (differenceFloor q)^2 := by
        apply sum_le_sum
        intro q hq
        have hj : differenceFloor q∈S := mem_image.mpr ⟨q,hq,rfl⟩
        exact pow_le_pow_left₀ (norm_nonneg _) ((hrep _ hj).2.2 q hq rfl) 2
      _ = _ := sum_differenceFloor_values W (fun j => v j^2)
  exact hOriginal.trans (hDyad.trans_eq (by dsimp only [F]; ring))

end Montgomery.RationalMoment
