module
public import DensityEnergyGM.SharpCountScale
public import TraceAlternatives.UniversalCountTraceExpansion
public import TraceAlternatives.UniversalCountAbsorption
public import TraceAlternatives.UniversalLowAbsorption
public import TraceAlternatives.UniversalTraceExpansion

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset GuthMaynard.Improvement GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- Actual general-polynomial count from the proved sharp trace and full
five-term energy. The only extra premises are explicit real exponent budgets.
The detector length and amplitude losses are tracked as144delta. -/
theorem universal_polynomial_count_loss {σ a δ : ℝ}
    (hσ : 4/5 ≤ σ) (hσ1 : σ < 1) (ha : 1/2 ≤ a) (ha1 : a < 2/3)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/1800) (hδa : δ ≤ (1-3*a/2)/2)
    (hm : ∀ x : ℝ, a ≤ x → ∀ j : Fin 3, ∀ i : Fin 5,
      0 ≤ universalTraceEnergyMargin σ a x j i)
    (hLowMargin : ∀ x : ℝ, a ≤ x → 1/100 ≤ universalLowMargin σ a x) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ T t₀ N : ℝ, T₀ ≤ T →
      T^a ≤ N → N ≤ T^(3*a/2+δ) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+144*δ) := by
  obtain ⟨A,hA,hQuad⟩ := finite_quadratic_large_value_universal MathCollab.Density.comparisonCutoff hδ
  obtain ⟨C,hC,hEnergy⟩ := discrete_energy_five_term_native δ hδ
  let B := (2*A)*(1+15*(1+C))
  have hB : 0 < B := by dsimp [B]; positivity
  let T₀ : ℝ := max 2 ((2*A)^200)
  have hT₀ : 2 ≤ T₀ := le_max_left _ _
  refine ⟨1+B^8,T₀,by positivity,hT₀,?_⟩
  intro T t₀ N hTall hlo hhi b hb W hW hSep hLarge
  have hT : 2 ≤ T := hT₀.trans hTall
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hN1 : 1 ≤ N := (Real.one_le_rpow hT1 (show 0 ≤ a by linarith)).trans hlo
  have hNp : 0 < N := by linarith
  obtain ⟨x,ell,hNx,hxa,hNL,hLT,hLs,hEll,hBase⟩ :=
    gm_detecting_scale hσ hσ1 ha ha1 hδ.le hδa (by linarith) hlo hhi
  have hLp : 0 < T^ell := by positivity
  have hRoot : Real.sqrt T ≤ N := by
    have hh : Real.sqrt T ≤ T^a := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hT1 ha
    exact hh.trans hlo
  have hTN : T ≤ N^2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg T) hRoot 2
    rwa [Real.sq_sqrt hTp.le] at h
  let V := N^σ*T^(-2*δ)
  let S := T^(3*a*(1-σ))
  let R : ℝ := W.card
  have hVp : 0 < V := by dsimp [V]; positivity
  have hSp : 0 < S := by dsimp [S]; positivity
  have hpδ : 1 ≤ T^δ := Real.one_le_rpow hT1 hδ.le
  have hOut : 1 ≤ 1+B^8 := by linarith [pow_nonneg hB.le 8]
  by_cases hRsmall : R ≤ S
  · have hPow : S ≤ T^(3*a*(1-σ)+144*δ) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    exact (hRsmall.trans hPow).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hOut
        (by positivity : 0 ≤ T^(3*a*(1-σ)+144*δ)))
  have hSR : S ≤ R := le_of_not_ge hRsmall
  have hRp : 0 < R := hSp.trans_le hSR
  have he := hEnergy T t₀ N b W V hT hNp hTN (hNL.trans hLT) hb hVp hLarge hSep hW
  have hq := hQuad T t₀ N (T^ell) hT hN1 hNL hLs hLT b hb W V hVp.le hW hLarge hSep
  have hTrace := universalTraceEnergy_common_bound hT1 hC.le (Nat.cast_nonneg (discreteAdditiveEnergy W))
    hδ.le hδ.le hSR hEll (hm x hxa) (by
      rw [← gm_amplitude_log_identity hTp,hNx]
      exact he)
  let X := S^(1/8:ℝ)*R^(15/8:ℝ)*V^4
  have hX : 0 < X := by dsimp [X]; positivity
  have hTrace' : (∑ j : Fin 3, N^3*T^(universalTraceA j)*(T^ell)^(universalTraceB j)*
      R^(universalTraceG j)*(discreteAdditiveEnergy W:ℝ)^(universalTraceD j)) ≤
      15*(1+C)*T^δ*(T^(16*δ)*X) := by
    rw [← gm_amplitude_log_identity hTp,hNx] at hTrace
    exact hTrace.trans_eq (by dsimp [X,S,V,R]; ring)
  have hLow0 : T^δ*N^3*T^(1/2:ℝ)*(T^ell)^(-1/2:ℝ) ≤
      T^(-1/200:ℝ)*V^4 := by
    dsimp only [V]
    rw [← hNx]
    exact universal_low_trace_budget hT1 hδsmall hEll (hLowMargin x hxa)
  have hCoeff : A*T^(-1/200:ℝ) ≤ 1/2 :=
    universal_low_coefficient_small hA hT ((le_max_right _ _).trans hTall)
  have hLow : A*T^δ*(N^3*T^(1/2:ℝ)*(T^ell)^(-1/2:ℝ)*R^2) ≤ (1/2)*(R^2*V^4) := by
    calc
      _ = A*(T^δ*N^3*T^(1/2:ℝ)*(T^ell)^(-1/2:ℝ))*R^2 := by ring
      _ ≤ A*(T^(-1/200:ℝ)*V^4)*R^2 := by gcongr
      _ = (A*T^(-1/200:ℝ))*(R^2*V^4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCoeff (by positivity)
  have hqFlat : R^2*V^4 ≤ A*T^δ*((N*T^ell)^2+
      N^3*T^(1/2:ℝ)*(T^ell)^(-1/2:ℝ)*R^2+
      ∑ j : Fin 3, N^3*T^(universalTraceA j)*(T^ell)^(universalTraceB j)*R^(universalTraceG j)*
        (discreteAdditiveEnergy W:ℝ)^(universalTraceD j)) := by
    exact hq.trans_eq (by rw [universalTraceExpression_eq hLp]; ring)
  have hq' : R^2*V^4 ≤ (2*A)*T^δ*((N*T^ell)^2+
      ∑ j : Fin 3, N^3*T^(universalTraceA j)*(T^ell)^(universalTraceB j)*R^(universalTraceG j)*
        (discreteAdditiveEnergy W:ℝ)^(universalTraceD j)) := by
    nlinarith only [hqFlat,hLow]
  have hS2 : S^2 ≤ S^(1/8:ℝ)*R^(15/8:ℝ) := by
    have hh := sublinear_monomial_domination hSp hSR (r := 0) (c := 1/8) (by norm_num)
    norm_num at hh
    exact hh
  have hBase' : (N*T^ell)^2 ≤ T^(16*δ)*X := by
    calc
      _ ≤ T^(10*δ)*S^2*V^4 := hBase
      _ ≤ T^(16*δ)*(S^(1/8:ℝ)*R^(15/8:ℝ))*V^4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hS2
          (sq_nonneg S) (by positivity)
      _ = _ := by dsimp [X]; ring
  have hPow : T^δ*T^δ*T^(16*δ)=T^(18*δ) := by
    rw [← Real.rpow_add hTp,← Real.rpow_add hTp]
    congr 1
    ring
  have hRaw : R^2*V^4 ≤ B*T^(18*δ)*X := by
    calc
      _ ≤ _ := hq'
      _ ≤ (2*A)*T^δ*(T^(16*δ)*X+15*(1+C)*T^δ*(T^(16*δ)*X)) := by gcongr
      _ ≤ (2*A)*T^δ*((1+15*(1+C))*T^δ*(T^(16*δ)*X)) := by
        have hh := mul_le_mul_of_nonneg_right hpδ
          (by positivity : 0 ≤ T^(16*δ)*X)
        nlinarith only [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (2*A)*T^δ)]
      _ = _ := by dsimp [B]; rw [← hPow]; ring
  have hCount : R^2 ≤ (B*T^(18*δ))*S^(1/8:ℝ)*R^(15/8:ℝ) := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < V^4)).mp
    dsimp [X] at hRaw
    nlinarith only [hRaw]
  have hAbs := eighth_gap_count_absorption hSp hSR hCount
  calc
    R ≤ (B*T^(18*δ))^8*S := hAbs
    _ = B^8*T^(3*a*(1-σ)+144*δ) := by
      rw [mul_pow,← Real.rpow_mul_natCast hTp.le]
      dsimp [S]
      rw [mul_assoc,← Real.rpow_add hTp]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Montgomery.RationalMoment
