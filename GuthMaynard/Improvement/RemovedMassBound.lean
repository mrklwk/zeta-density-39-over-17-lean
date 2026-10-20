module
public import GuthMaynard.Improvement.RemovedMassDyadic
public import GuthMaynard.Improvement.ClassicalLevelVolume
public import GuthMaynard.Improvement.SourceRatioHeightBudget
public import GuthMaynard.Improvement.FixedCutoffs

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- A bounded cutoff costs no more than the actual level volume on its support. -/
theorem weighted_level_integral_le_volume {β : ℝ → ℝ} (hβi : Integrable β)
    (hβ1 : ∀ t, β t ≤ 1)
    {a b : ℝ} (hs : Function.support β ⊆ Icc a b)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ t, E.indicator β t) ≤ volume.real (E ∩ Icc a b) := by
  have hmeas : MeasurableSet (E ∩ Icc a b) := hE.inter measurableSet_Icc
  have hfinite : volume (E ∩ Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_right)
  have hi : Integrable ((E ∩ Icc a b).indicator (fun _ : ℝ => (1:ℝ))) :=
    (integrableOn_const hfinite).integrable_indicator hmeas
  calc
    _ ≤ ∫ t, (E ∩ Icc a b).indicator (fun _ : ℝ => (1:ℝ)) t := by
      apply integral_mono (hβi.indicator hE) hi
      intro t
      by_cases ht : t ∈ E
      · by_cases hc : t ∈ Icc a b
        · simpa [ht,hc] using hβ1 t
        · have hz : β t=0 := by
            by_contra hn
            exact hc (hs hn)
          simp [ht,hc,hz]
      · simp [ht]
    _ = _ := by rw [integral_indicator_const _ hmeas]; simp

/-- The sixth-power classical tail contributes an exact geometric ratio 1/16. -/
theorem removed_dyadic_classical_sum {N T U : ℝ} (hT : 0 ≤ T) (hU : 0 < U)
    (J : ℕ) :
    (∑ j ∈ Finset.range J, 4*((2:ℝ)^j*U)^2*
      (N^2/((2:ℝ)^j*U)^2+T*N^4/((2:ℝ)^j*U)^6)) ≤
      4*(J:ℝ)*N^2+8*T*N^4/U^4 := by
  have hid (j : ℕ) : 4*((2:ℝ)^j*U)^2*
      (N^2/((2:ℝ)^j*U)^2+T*N^4/((2:ℝ)^j*U)^6) =
      4*N^2+(4*T*N^4/U^4)*(1/16:ℝ)^j := by
    have hg : (1/16:ℝ)^j = 1/((2:ℝ)^j)^4 := by
      rw [← pow_mul, Nat.mul_comm j 4, pow_mul, one_div_pow]
      norm_num
    rw [hg]
    field_simp
  simp_rw [hid]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hg := geom_sum_mul (1/16:ℝ) J
  have hgp : 0 ≤ (1/16:ℝ)^J := by positivity
  have hsum : (∑ j ∈ Finset.range J, (1/16:ℝ)^j) ≤ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4*T*N^4/U^4 by positivity)
  convert add_le_add_left hh ((J:ℝ)*(4*N^2)) using 1 <;> ring

/-- A dyadic cover of the uniform polynomial bound with a subpower shell count. -/
theorem removed_dyadic_cover {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 2 ≤ N →
      ∃ J : ℕ, 2*N ≤ (2:ℝ)^J ∧ (J:ℝ)+1 ≤ K*N^δ := by
  let K := (2/Real.log 2)*(Real.log 2+1/δ)+1
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro N hN
  have hn : 0 < N := by linarith
  obtain ⟨J,hcover,_,hupper,_⟩ := source_least_height_cover
    (X := 2*N) (Y := 1) (by norm_num) (by linarith)
  simp only [mul_one] at hcover hupper
  have hjlog : (J:ℝ)*Real.log 2 ≤ 2*Real.log (2*N) := by
    have hh := Real.log_lt_log (by positivity : 0 < (2:ℝ)^J) hupper
    rw [Real.log_pow] at hh
    have he : Real.log (2*(2*N)) = Real.log 2+Real.log (2*N) :=
      Real.log_mul (by norm_num) (by positivity)
    rw [he] at hh
    have hm : Real.log 2 ≤ Real.log (2*N) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hj : (J:ℝ) ≤ (2/Real.log 2)*Real.log (2*N) := by
    have hh := (le_div_iff₀ hl).mpr hjlog
    convert hh using 1
    ring
  have hg := classical_log_budget (show 1 ≤ N by linarith) hδ
  have hnp : 1 ≤ N^δ := Real.one_le_rpow (by linarith) hδ.le
  have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2/Real.log 2 by positivity)
  refine ⟨J,hcover,?_⟩
  dsimp [K]
  nlinarith

/-- Actual removed mass with fixed cutoff and no classical-estimate premise. -/
theorem fixed_source_removed_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T U : ℝ,
      2 ≤ N → N ≤ T → T ≤ N^2 → 1 ≤ U →
      ∀ a : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∫ t, sourceRemovedDensity (fun t => fixedTimeCutoff (t/T))
        (boundedPolynomial N a) U t) ≤ C*N^ε*(N^2+T*N^4/U^4) := by
  have he : 0 < ε/2 := by linarith
  obtain ⟨C,hC,hlevels⟩ := boundedPolynomial_classical_level_volume he
  obtain ⟨K,hK,hcover⟩ := removed_dyadic_cover he
  refine ⟨40*C*K,by positivity,?_⟩
  intro N T U hN hNT hTN hU a ha
  have hn : 0 < N := by linarith
  have ht : 0 < T := by linarith
  have hu : 0 < U := by linarith
  let β := fun t => fixedTimeCutoff (t/T)
  let D := boundedPolynomial N a
  have hβm : Measurable β :=
    (fixedTimeCutoff_smooth.continuous.comp (continuous_id.div_const T)).measurable
  have hβi : Integrable β := by
    simpa [β,div_eq_mul_inv,mul_comm] using
      (fixedTimeCutoff_smooth.continuous.integrable_of_hasCompactSupport
        fixedTimeCutoff_compact).comp_mul_left' (inv_ne_zero ht.ne')
  have hβ0 : ∀ t, 0 ≤ β t := fun t => (fixedTimeCutoff_bounds (t/T)).1
  have hβ1 : ∀ t, β t ≤ 1 := fun t => (fixedTimeCutoff_bounds (t/T)).2
  have hs : Function.support β ⊆ Icc (-2*T) (3*T) := by
    intro t hmem
    have hh := fixedTimeCutoff_support (subset_closure hmem)
    exact ⟨(le_div_iff₀ ht).mp hh.1,(div_le_iff₀ ht).mp hh.2⟩
  have hDm : Measurable D := (boundedPolynomial_regular N a).1.measurable
  obtain ⟨J,hJ,hJK⟩ := hcover N hN
  have hb : ∀ t, ‖D t‖ ≤ (2:ℝ)^J*U := by
    intro t
    exact (boundedPolynomial_norm_le_two_mul hN a ha t).trans
      (hJ.trans (le_mul_of_one_le_right (by positivity) hU))
  have hlev (j : ℕ) : (∫ t, {t | (2:ℝ)^j*U < ‖D t‖}.indicator β t) ≤
      5*C*N^(ε/2)*(N^2/((2:ℝ)^j*U)^2+T*N^4/((2:ℝ)^j*U)^6) := by
    have hV : 0 < (2:ℝ)^j*U := by positivity
    have hh := hlevels N T ((2:ℝ)^j*U) (-2*T) hN hNT hTN hV a ha 5
    norm_num only [Nat.cast_ofNat] at hh
    have hend : -2*T+5*T=3*T := by ring
    rw [hend] at hh
    exact (weighted_level_integral_le_volume hβi hβ1 hs
      (measurableSet_lt measurable_const hDm.norm)).trans hh
  have hraw := source_removed_mass_dyadic hβm hβi hβ0 hβ1 hDm J hb
  have hsum : (∑ j ∈ Finset.range J, 4*((2:ℝ)^j*U)^2*
      (∫ t, {t | (2:ℝ)^j*U < ‖D t‖}.indicator β t)) ≤
      (5*C*N^(ε/2))*(4*(J:ℝ)*N^2+8*T*N^4/U^4) := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, 4*((2:ℝ)^j*U)^2*
          (5*C*N^(ε/2)*(N^2/((2:ℝ)^j*U)^2+T*N^4/((2:ℝ)^j*U)^6)) := by
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hlev j) (by positivity)
      _ = (5*C*N^(ε/2))*(∑ j ∈ Finset.range J, 4*((2:ℝ)^j*U)^2*
          (N^2/((2:ℝ)^j*U)^2+T*N^4/((2:ℝ)^j*U)^6)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (removed_dyadic_classical_sum ht.le hu J) (by positivity)
  have hp : N^(ε/2)*N^(ε/2)=N^ε := by rw [← Real.rpow_add hn]; congr 1; ring
  have hrest : 0 ≤ T*N^4/U^4 := by positivity
  have hscalar : 4*(J:ℝ)*N^2+8*T*N^4/U^4 ≤
      8*(K*N^(ε/2))*(N^2+T*N^4/U^4) := by
    have hj0 : (0:ℝ) ≤ J := by positivity
    have h1 : 1 ≤ K*N^(ε/2) := by linarith
    have h2 := mul_le_mul_of_nonneg_right
      (show 4*(J:ℝ) ≤ 8*(K*N^(ε/2)) by linarith) (sq_nonneg N)
    have h3 := mul_le_mul_of_nonneg_right h1 hrest
    have hh := add_le_add h2 (mul_le_mul_of_nonneg_left h3 (show (0:ℝ) ≤ 8 by norm_num))
    convert hh using 1 <;> ring
  calc
    _ ≤ (5*C*N^(ε/2))*(4*(J:ℝ)*N^2+8*T*N^4/U^4) := hraw.trans hsum
    _ ≤ (5*C*N^(ε/2))*(8*(K*N^(ε/2))*(N^2+T*N^4/U^4)) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by
      calc
        _ = 40*C*K*(N^(ε/2)*N^(ε/2))*(N^2+T*N^4/U^4) := by ring
        _ = _ := by rw [hp]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.weighted_level_integral_le_volume
#print axioms GuthMaynard.Improvement.removed_dyadic_classical_sum
#print axioms GuthMaynard.Improvement.removed_dyadic_cover
#print axioms GuthMaynard.Improvement.fixed_source_removed_mass
