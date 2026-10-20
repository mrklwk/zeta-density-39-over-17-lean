module
public import GuthMaynard.Improvement.UpperCurveDensity
public import GuthMaynard.Improvement.CombinedDensityCurve

@[expose] public section

open Real Complex Set Filter Finset MathCollab.Density GuthMaynard.Improvement
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
noncomputable section
namespace Montgomery.Refined

/-- New bounds for the moving powered window on the upper interval. -/
theorem refined_scale_bounds {σ : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) :
    8/11 ≤ shortDensityA σ ∧ shortDensityA σ ≤ 4/5 ∧
    0 ≤ shortDensityB σ ∧ shortDensityB σ ≤ 6/5 ∧
    0 < shortDensityExponent σ ∧
    2-2*σ+1/25 ≤ shortDensityExponent σ := by
  have hd : 0 < 7*σ+3 := by linarith
  have ha : 8/11 ≤ shortDensityA σ := by
    unfold shortDensityA
    apply (le_div_iff₀ hd).mpr
    linarith
  have ha' : shortDensityA σ ≤ 4/5 := by
    unfold shortDensityA
    apply (div_le_iff₀ hd).mpr
    linarith
  refine ⟨ha,ha',?_,?_,?_,?_⟩
  · unfold shortDensityB; linarith
  · unfold shortDensityB; linarith
  · unfold shortDensityExponent
    exact div_pos (by linarith) hd
  · have hg : 2-2*σ+1/22 ≤ shortDensityExponent σ := by
      unfold shortDensityExponent
      apply (le_div_iff₀ hd).mpr
      nlinarith [mul_nonneg_of_nonpos_of_nonpos
        (show 4*σ-3 ≤ 0 by linarith) (show 77*σ-87 ≤ 0 by linarith)]
    linarith

def refinedSplit (σ : ℝ) : ℝ := (25*σ-15)/((7*σ+3)*(2*σ-1))

theorem refined_split_bounds {σ : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) :
    5/6 ≤ refinedSplit σ ∧ refinedSplit σ ≤ 10/11 := by
  have hd : 0 < (7*σ+3)*(2*σ-1) := mul_pos (by linarith) (by linarith)
  unfold refinedSplit
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ 7*σ-5 by linarith)
      (show 0 ≤ 3-2*σ by linarith)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg_of_nonpos_of_nonpos
      (show 4*σ-3 ≤ 0 by linarith) (show 7*σ-9 ≤ 0 by linarith)]

theorem refined_split_budgets {σ : ℝ} (hσ : 5/7 ≤ σ) (_hσ' : σ ≤ 3/4) :
    refinedSplit σ*(18/5-4*σ) ≤ shortDensityExponent σ ∧
    1+refinedSplit σ*(1-2*σ) = shortDensityExponent σ := by
  have hd : 0 < (7*σ+3)*(2*σ-1) := mul_pos (by linarith) (by linarith)
  have hne : 7*σ+3 ≠ 0 := by linarith
  have hne' : 2*σ-1 ≠ 0 := by linarith
  constructor
  · have hid : shortDensityExponent σ-refinedSplit σ*(18/5-4*σ) =
        4*(4*σ-3)^2/((7*σ+3)*(2*σ-1)) := by
      unfold shortDensityExponent refinedSplit
      field_simp [hne, hne', show -1+σ*2 ≠ 0 by linarith]
      ring_nf
      field_simp [hne, hne', show -1+σ*2 ≠ 0 by linarith]
      ring
    have hh : 0 ≤ shortDensityExponent σ-refinedSplit σ*(18/5-4*σ) := by
      rw [hid]
      positivity
    linarith
  · unfold shortDensityExponent refinedSplit
    field_simp [hne, hne', show -1+σ*2 ≠ 0 by linarith]
    ring_nf
    field_simp [hne, hne', show -1+σ*2 ≠ 0 by linarith]
    ring

theorem refined_length_budgets {σ H N δ : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H) (hN : 0 ≤ N)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/100) (hhi : N ≤ H^(shortDensityB σ+δ)) :
    N^δ ≤ H^(2*δ) ∧
    N^(2-2*σ) ≤ H^(shortDensityExponent σ+2*δ) := by
  have hH0 : 0 < H := by linarith
  have hB := (refined_scale_bounds hσ hσ').2.2.2.1
  have hid := (short_density_scale_identities (show 9/13 ≤ σ by linarith)).1
  constructor
  · calc
      _ ≤ (H^(shortDensityB σ+δ))^δ := Real.rpow_le_rpow hN hhi hδ
      _ = H^((shortDensityB σ+δ)*δ) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH
        (mul_le_mul_of_nonneg_right (by linarith : shortDensityB σ+δ ≤ 2) hδ)
  · calc
      _ ≤ (H^(shortDensityB σ+δ))^(2-2*σ) := Real.rpow_le_rpow hN hhi (by linarith)
      _ = H^((shortDensityB σ+δ)*(2-2*σ)) := (Real.rpow_mul hH0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (by
        nlinarith [mul_nonneg hδ (show 0 ≤ σ by linarith)])

theorem refined_padded_time {σ H N : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H) (hN : 2 ≤ N)
    (hlo : H^(shortDensityA σ) ≤ N) (hhi : N ≤ H^(refinedSplit σ)) :
    ∃ S : ℝ, N^(6/5:ℝ) ≤ S ∧ S ≤ N^(5/3:ℝ) ∧ H ≤ S ∧
      N^(18/7-4*σ)*S^(6/7:ℝ) ≤ H^(shortDensityExponent σ) := by
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have ha := (refined_scale_bounds hσ hσ').1
  have hid := (short_density_scale_identities (show 9/13 ≤ σ by linarith)).2
  by_cases hm : N ≤ H^(5/6:ℝ)
  · refine ⟨H,?_,?_,le_rfl,?_⟩
    · calc
        _ ≤ (H^(5/6:ℝ))^(6/5:ℝ) := Real.rpow_le_rpow hN0.le hm (by norm_num)
        _ = H := by rw [← Real.rpow_mul hH0.le]; norm_num
    · calc
        H = H^(1:ℝ) := (Real.rpow_one H).symm
        _ ≤ H^(shortDensityA σ*(5/3:ℝ)) := Real.rpow_le_rpow_of_exponent_le hH (by linarith)
        _ = (H^(shortDensityA σ))^(5/3:ℝ) := Real.rpow_mul hH0.le _ _
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hlo (by norm_num)
    · calc
        _ ≤ (H^(shortDensityA σ))^(18/7-4*σ)*H^(6/7:ℝ) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos
            (by positivity) hlo (by linarith)) (by positivity)
        _ = H^(shortDensityA σ*(18/7-4*σ)+6/7) := by
          rw [← Real.rpow_mul hH0.le,← Real.rpow_add hH0]
        _ = _ := by rw [hid]
  · refine ⟨N^(6/5:ℝ),le_rfl,?_,?_,?_⟩
    · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    · calc
        H = (H^(5/6:ℝ))^(6/5:ℝ) := by rw [← Real.rpow_mul hH0.le]; norm_num
        _ ≤ _ := Real.rpow_le_rpow (by positivity) (le_of_not_ge hm) (by norm_num)
    · calc
        _ = N^(18/5-4*σ) := by
          rw [← Real.rpow_mul hN0.le,← Real.rpow_add hN0]; congr 1; ring
        _ ≤ (H^(refinedSplit σ))^(18/5-4*σ) :=
          Real.rpow_le_rpow hN0.le hhi (by linarith)
        _ = H^(refinedSplit σ*(18/5-4*σ)) := by rw [← Real.rpow_mul hH0.le]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (refined_split_budgets hσ hσ').1

theorem refined_mean_budget {σ H N : ℝ}
    (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hH : 1 ≤ H)
    (hlo : H^(refinedSplit σ) ≤ N) :
    H*N^(1-2*σ) ≤ H^(shortDensityExponent σ) := by
  have hH0 : 0 < H := by linarith
  calc
    _ ≤ H*(H^(refinedSplit σ))^(1-2*σ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith)) hH0.le
    _ = H^(1+refinedSplit σ*(1-2*σ)) := by
      rw [← Real.rpow_mul hH0.le]
      nth_rw 1 [← Real.rpow_one H]
      rw [← Real.rpow_add hH0]
    _ = _ := by rw [(refined_split_budgets hσ hσ').2]
/-- Uniform logarithmic buffer for the entire compact target exponent range. -/
theorem refined_power_buffer_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ a : ℝ, 8/11 ≤ a → a ≤ 4/5 →
      T*(Real.log T)^4 ≤ T^(3*a/2) ∧
      (2:ℝ)^100*T^(3*a/2) ≤ T^2 := by
  have hl := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (show (0:ℝ)<1/11 by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hl.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    (tendsto_rpow_atTop (show (0:ℝ)<4/5 by norm_num)).eventually_ge_atTop ((2:ℝ)^100)]
    with T hT hlog hconst
  intro a ha ha'
  have ht : 0 < T := by linarith
  constructor
  · have hb : (Real.log T)^4 ≤ T^(1/11:ℝ) :=
      ((div_lt_one (by positivity)).mp hlog).le
    calc
      _ ≤ T*T^(1/11:ℝ) := mul_le_mul_of_nonneg_left hb ht.le
      _ = T^(12/11:ℝ) := by
        nth_rw 1 [← Real.rpow_one T]
        rw [← Real.rpow_add ht]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  · calc
      _ ≤ T^(4/5:ℝ)*T^(3*a/2) := mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = T^((4/5:ℝ)+3*a/2) := by rw [← Real.rpow_add ht]
      _ ≤ T^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = T^2 := Real.rpow_two T

/-- Actual short detection yields a bounded-coefficient powered family in the
full target window, without moving the ordinate. No counting estimate is assumed. -/
theorem refined_powered_cover {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      ((shortPoweredDetectorIndices T).card:ℝ) ≤ 600000*(Real.log T)^2 ∧
      ∀ (a σ : ℝ) (ρ : ℂ), 8/11 ≤ a → a ≤ 4/5 →
        0 ≤ σ → σ ≤ ρ.re → ρ.re ≤ 1 → 1/3 ≤ ‖shortFiniteDetector ρ T‖ →
        ∃ p ∈ shortPoweredDetectorIndices T,
          T^a ≤ (shortPoweredDetectorScale p:ℝ) ∧
          (shortPoweredDetectorScale p:ℝ) ≤ (2:ℝ)^99*T^(3*a/2) ∧
          2*(shortPoweredDetectorScale p:ℝ) ≤ T^2 ∧
          (shortPoweredDetectorScale p:ℝ)^σ*T^(-2*η) ≤
            ‖detectingPolynomial (shortPoweredDetectorScale p)
              (shortPoweredDetectorFamilyCoeff η T p) ρ.im‖ := by
  filter_upwards [eventually_gt_atTop (1:ℝ), shortFiniteDetector_fixed_family_eventually,
    refined_power_buffer_eventually, exists_shortNormalizedPowered_height hη]
    with T hT hf hb hh
  refine ⟨shortPoweredDetectorIndices_card_le hf.1, ?_⟩
  intro a σ ρ ha ha' hσ hσβ hβ hlarge
  obtain ⟨q,hq,hlo,hhi,hd⟩ := hf.2 σ ρ hσ hσβ hβ hlarge
  obtain ⟨k,hk,hk100,hklo,hkhi⟩ := short_detector_power_exists hT
    (by linarith) (by linarith) hlo hhi.le (hb a ha ha').1
  obtain ⟨ℓ,hℓ,hheight⟩ := hh σ ρ.im (2^q.1) q.2 k (by positivity)
    hσ (hσβ.trans hβ) hk hk100 hd
  have hs := short_detector_power_piece_bounds hk100 (Finset.mem_range.mp hℓ)
    hklo hkhi (hb a ha ha').2
  refine ⟨(q,(k,ℓ)), Finset.mem_product.mpr ⟨hq, Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hk,hk100⟩, Finset.mem_range.mpr (by change ℓ < 100; have := Finset.mem_range.mp hℓ; omega)⟩⟩,
    hs.1, hs.2.1, hs.2.2, hheight⟩


/-- Actual large values for sigma in [5/7,3/4]. The intermediate lengths
pad the observation time to N^(6/5), preserving the original threshold and
finite set. The middle theorem is invoked only within its proved range. -/
theorem refined_large_values {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ H N t₀ : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
      5/7 ≤ σ → σ ≤ 3/4 → 2 ≤ H → 2 ≤ N →
      H^(shortDensityA σ) ≤ N → N ≤ H^(shortDensityB σ+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*H^(shortDensityExponent σ+10*δ) := by
  obtain ⟨C,hC,hmid⟩ := middle_range_large_values δ hδ
  let D : ℝ := Real.log 2+1/δ
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hδ)
  refine ⟨2*C+102*(1+D),by positivity,?_⟩
  intro σ H N t₀ a W hσ hσ' hH hN hlo hhi ha hloc hsep hlarge
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hV : 0 < N^σ*H^(-2*δ) := by positivity
  obtain ⟨hsmall,hpos⟩ := refined_length_budgets hσ hσ' hH1 hN0.le hδ.le hδ' hhi
  obtain ⟨hdiv2,_hdiv4,hdivM⟩ := short_density_height_budgets hH0 hN0 σ δ
  have hp : 0 ≤ H^(shortDensityExponent σ+10*δ) := by positivity
  by_cases hm : N ≤ H^(refinedSplit σ)
  · obtain ⟨S,htlo,hthi,hHS,hquartic⟩ := refined_padded_time hσ hσ' hH1 hN hlo hm
    have hS0 : 0 < S := hH0.trans_le hHS
    have hlocS : ∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+S := by
      intro t ht
      exact ⟨(hloc t ht).1,by linarith [(hloc t ht).2]⟩
    have hc := hmid N S (N^σ*H^(-2*δ)) t₀ a W hN htlo hthi hV ha hlocS hsep hlarge
    rw [hdiv2,upper_window_padded_denominator hH0 hN0 S σ δ] at hc
    have hb2 : N^(2-2*σ)*H^(4*δ) ≤ H^(shortDensityExponent σ+8*δ) := by
      calc
        _ ≤ H^(shortDensityExponent σ+2*δ)*H^(4*δ) :=
          mul_le_mul_of_nonneg_right hpos (by positivity)
        _ = H^(shortDensityExponent σ+6*δ) := by
          rw [← Real.rpow_add hH0]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    have hb4 : (N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ) ≤
        H^(shortDensityExponent σ+8*δ) := by
      calc
        _ ≤ H^(shortDensityExponent σ)*H^(8*δ) :=
          mul_le_mul_of_nonneg_right hquartic (by positivity)
        _ = _ := (Real.rpow_add hH0 _ _).symm
    have hsum : N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ) ≤
        2*H^(shortDensityExponent σ+8*δ) := by linarith
    have hbudget : C*N^δ*(N^(2-2*σ)*H^(4*δ)+(N^(18/7-4*σ)*S^(6/7:ℝ))*H^(8*δ)) ≤
        (2*C)*H^(shortDensityExponent σ+10*δ) := by
      calc
        _ ≤ (C*H^(2*δ))*(2*H^(shortDensityExponent σ+8*δ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsmall hC.le) hsum (by positivity) (by positivity)
        _ = (2*C)*(H^(2*δ)*H^(shortDensityExponent σ+8*δ)) := by ring
        _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring
    exact (hc.trans hbudget).trans
      (mul_le_mul_of_nonneg_right (by linarith : 2*C ≤ 2*C+102*(1+D)) hp)
  · have hmean := separated_second_moment hN hH0.le a ha W hloc hsep
    have hcard : (W.card:ℝ)*(N^σ*H^(-2*δ))^2 ≤ 102*N*(H+N*Real.log (2*N)) := by
      calc
        _ = ∑ _t ∈ W, (N^σ*H^(-2*δ))^2 := by simp
        _ ≤ ∑ t ∈ W, ‖boundedPolynomial N a t‖^2 :=
          sum_le_sum (fun t ht => pow_le_pow_left₀ hV.le (hlarge t ht) 2)
        _ ≤ _ := hmean
    have hc : (W.card:ℝ) ≤ 102*((H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N))*H^(4*δ)) := by
      have hh := (le_div_iff₀ (sq_pos_of_pos hV)).mpr hcard
      have he : 102*N*(H+N*Real.log (2*N))/(N^σ*H^(-2*δ))^2 =
          102*(N*(H+N*Real.log (2*N))/(N^σ*H^(-2*δ))^2) := by ring
      rw [he,hdivM] at hh
      exact hh
    have hlog : Real.log (2*N) ≤ D*H^(2*δ) :=
      (classical_log_budget (by linarith : 1 ≤ N) hδ).trans
        (mul_le_mul_of_nonneg_left hsmall hD.le)
    have hmean1 := refined_mean_budget hσ hσ' hH1 (le_of_not_ge hm)
    have hmean2 : N^(2-2*σ)*Real.log (2*N) ≤ D*H^(shortDensityExponent σ+4*δ) := by
      calc
        _ ≤ H^(shortDensityExponent σ+2*δ)*(D*H^(2*δ)) :=
          mul_le_mul hpos hlog (Real.log_nonneg (by linarith)) (by positivity)
        _ = D*(H^(shortDensityExponent σ+2*δ)*H^(2*δ)) := by ring
        _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring
    have hmean1' : H*N^(1-2*σ) ≤ H^(shortDensityExponent σ+4*δ) :=
      hmean1.trans (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))
    have hsum : H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N) ≤
        (1+D)*H^(shortDensityExponent σ+4*δ) := by nlinarith
    have hbudget : 102*((H*N^(1-2*σ)+N^(2-2*σ)*Real.log (2*N))*H^(4*δ)) ≤
        (102*(1+D))*H^(shortDensityExponent σ+10*δ) := by
      calc
        _ ≤ 102*(((1+D)*H^(shortDensityExponent σ+4*δ))*H^(4*δ)) := by gcongr
        _ = (102*(1+D))*(H^(shortDensityExponent σ+4*δ)*H^(4*δ)) := by ring
        _ = (102*(1+D))*H^(shortDensityExponent σ+8*δ) := by
          rw [← Real.rpow_add hH0]; congr 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)) (by positivity)
    exact (hc.trans hbudget).trans
      (mul_le_mul_of_nonneg_right (by linarith : 102*(1+D) ≤ 2*C+102*(1+D)) hp)

/-- Actual Type-I detection of an ordinate-injective separated finite family.
The constant and height threshold precede sigma, translation and the family. -/
theorem refined_typeI_separated_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ t₀ : ℝ) (R : Finset ℂ),
      5/7 ≤ σ → σ ≤ 3/4 →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ.im ∈ Icc t₀ (t₀+H) ∧
        (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(shortDensityExponent σ+ε) := by
  classical
  let η : ℝ := min (ε/100) (1/100)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ 1/100 := min_le_right _ _
  have hηeps : η ≤ ε/100 := min_le_left _ _
  obtain ⟨C,hC,hLV⟩ := refined_large_values hη hηsmall
  have hloglim := (isLittleO_log_rpow_rpow_atTop (2:ℝ) hη).tendsto_div_nhds_zero
  norm_num at hloglim
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ), refined_powered_cover hη,
    shortPoweredDetectorFamily_coefficients hη,
    (tendsto_rpow_atTop hη).eventually_ge_atTop ((2:ℝ)^99),
    (tendsto_rpow_atTop (show (0:ℝ)<8/11 by norm_num)).eventually_ge_atTop 2,
    hloglim.eventually (gt_mem_nhds (show (0:ℝ)<1/600000 by norm_num))]
    with H hH hfamily hcoeff hconst hlength hlog
  intro σ t₀ R hσ hσ' hcard hsep hR
  have hHpos : 0 < H := by linarith
  have hHa : 1 ≤ H := by linarith
  have hsc := refined_scale_bounds hσ hσ'
  let J := (shortPoweredDetectorIndices H).filter (fun p =>
    H^(shortDensityA σ) ≤ (shortPoweredDetectorScale p:ℝ) ∧
    (shortPoweredDetectorScale p:ℝ) ≤ (2:ℝ)^99*H^(shortDensityB σ) ∧
    2*(shortPoweredDetectorScale p:ℝ) ≤ H^2)
  let W := R.image Complex.im
  let Wj := fun p => W.filter (fun t =>
    (shortPoweredDetectorScale p:ℝ)^σ*H^(-2*η) ≤
      ‖detectingPolynomial (shortPoweredDetectorScale p) (shortPoweredDetectorFamilyCoeff η H p) t‖)
  have hWj : ∀ p ∈ J, ((Wj p).card:ℝ) ≤ C*H^(shortDensityExponent σ+10*η) := by
    intro p hp
    obtain ⟨hp,hlow,hhigh,hsupport⟩ := Finset.mem_filter.mp hp
    have hN : 2 ≤ (shortPoweredDetectorScale p:ℝ) :=
      hlength.trans ((Real.rpow_le_rpow_of_exponent_le hHa hsc.1).trans hlow)
    have hupper : (shortPoweredDetectorScale p:ℝ) ≤ H^(shortDensityB σ+η) := by
      calc
        _ ≤ (2:ℝ)^99*H^(shortDensityB σ) := hhigh
        _ ≤ H^η*H^(shortDensityB σ) := mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = _ := by rw [← Real.rpow_add hHpos]; congr 1; ring
    have hc : ∀ n ∈ sourceRatioIndices (shortPoweredDetectorScale p:ℝ),
        ‖shortPoweredDetectorFamilyCoeff η H p n‖ ≤ 1 := by
      intro n hn
      apply hcoeff p hp hsupport n
      simpa only [sourceRatioIndices, show 2*(shortPoweredDetectorScale p:ℝ) =
        ((2*shortPoweredDetectorScale p:ℕ):ℝ) by push_cast; rfl, Nat.floor_natCast] using hn
    apply hLV σ H (shortPoweredDetectorScale p:ℝ) t₀
      (shortPoweredDetectorFamilyCoeff η H p) (Wj p) hσ hσ' hH hN hlow hupper hc
    · intro t ht
      obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
      exact (hR ρ hρ).2.2.1
    · intro t ht s hs hne
      exact hsep t (Finset.mem_filter.mp ht).1 s (Finset.mem_filter.mp hs).1 hne
    · intro t ht
      simpa only [← detectingPolynomial_eq_boundedPolynomial] using (Finset.mem_filter.mp ht).2
  have hcover : W ⊆ J.biUnion Wj := by
    intro t ht
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hβ,hβ',_hloc,hd⟩ := hR ρ hρ
    obtain ⟨p,hp,hlo,hhi,hsupport,hlarge⟩ := hfamily.2 (shortDensityA σ) σ ρ
      hsc.1 hsc.2.1 (by linarith) hβ hβ' hd
    apply Finset.mem_biUnion.mpr
    refine ⟨p,Finset.mem_filter.mpr ⟨hp,hlo,hhi,hsupport⟩,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨ρ,hρ,rfl⟩,hlarge⟩
  have hJ : (J.card:ℝ) ≤ H^η := by
    have hsmall : 600000*(Real.log H)^2 ≤ H^η := by
      have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hHpos η)).mp hlog
      linarith
    exact (show (J.card:ℝ) ≤ (shortPoweredDetectorIndices H).card by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)).trans (hfamily.1.trans hsmall)
  have hsum : (W.card:ℝ) ≤ (J.card:ℝ)*(C*H^(shortDensityExponent σ+10*η)) := by
    calc
      _ ≤ ∑ p ∈ J, ((Wj p).card:ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ J, C*H^(shortDensityExponent σ+10*η) := Finset.sum_le_sum hWj
      _ = _ := by simp
  have hpow : H^(shortDensityExponent σ+11*η) ≤ H^(shortDensityExponent σ+ε) :=
    Real.rpow_le_rpow_of_exponent_le hHa (by linarith)
  calc
    _ = (W.card:ℝ) := by rw [hcard]
    _ ≤ (J.card:ℝ)*(C*H^(shortDensityExponent σ+10*η)) := hsum
    _ ≤ H^η*(C*H^(shortDensityExponent σ+10*η)) :=
      mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = C*H^(shortDensityExponent σ+11*η) := by
      rw [← mul_left_comm, ← Real.rpow_add hHpos]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hC.le

/-- The Type-I branch count on actual zero-slab representatives. -/
theorem refined_typeI_zero_slab_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ : ℝ) (R : Finset ℂ),
      5/7 ≤ σ → σ ≤ 3/4 → R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖) →
      (R.card:ℝ) ≤ C*H^(shortDensityExponent σ+ε) := by
  obtain ⟨C,hC,hcount⟩ := refined_typeI_separated_count hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with H hh
  intro σ R hσ hσ' hR hcard hsep hlarge
  apply hh σ H R hσ hσ' hcard hsep
  intro ρ hρ
  obtain ⟨hz,hβ,hγ,hγ'⟩ := mem_zetaZeroFinset.mp (hR hρ)
  exact ⟨hβ,hz.2.2.le,⟨hγ,by linarith⟩,hlarge ρ hρ⟩

/-- Uniform actual slab density, using the proved weaker moment.
Both separated branch estimates, contour detection and analytic multiplicity
restoration are proved dependencies. -/
theorem refined_slab_density
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ σ : ℝ,
      5/7 ≤ σ → σ ≤ 3/4 →
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*H^((shortDensityExponent σ)+ε) := by
  have hη : 0 < ε/2 := by positivity
  obtain ⟨CI,hCI,hI⟩ := refined_typeI_zero_slab_count hη
  obtain ⟨CII,hCII,hII⟩ := weak_short_typeII_zero_slab_count hη
  obtain ⟨C₀,hC₀,hrestore⟩ := short_slab_count_of_separated_branch_bounds
  let D : ℝ := Real.log 2+1/(ε/2)
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num)) (one_div_pos.mpr hη)
  refine ⟨C₀*(CI+CII)*D,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),hI,hII,hrestore] with H hH hi hii hr
  intro σ hσ hσ'
  have hσ₀ : 9/13 ≤ σ := by linarith
  have hIIexp := (refined_scale_bounds hσ hσ').2.2.2.2.2
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hb := hr σ (CI*H^((shortDensityExponent σ)+ε/2))
    (CII*H^((shortDensityExponent σ)+ε/2)) hσ₀ (fun R hR hc hs hl => hi σ R hσ hσ' hR hc hs hl) (by
      intro R hR hc hs hl
      exact (hii σ R hσ₀ hR hc hs hl).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH1
          (by linarith)) hCII.le))
  have hlog : Real.log (2*H) ≤ D*H^(ε/2) := classical_log_budget hH1 hη
  calc
    _ ≤ C₀*Real.log (2*H)*(CI*H^((shortDensityExponent σ)+ε/2)+CII*H^((shortDensityExponent σ)+ε/2)) := hb
    _ ≤ C₀*(D*H^(ε/2))*(CI*H^((shortDensityExponent σ)+ε/2)+CII*H^((shortDensityExponent σ)+ε/2)) := by gcongr
    _ = (C₀*(CI+CII)*D)*(H^(ε/2)*H^((shortDensityExponent σ)+ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring

/-- All actual zeros with analytic multiplicity and both signs. The audited
fixed-sigma dyadic summation is reused, so this constant may depend on sigma. -/
theorem refined_density
    {σ ε : ℝ} (hσ : 5/7 ≤ σ) (hσ' : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(shortDensityExponent σ+ε) := by
  obtain ⟨C,hC,hslab⟩ := refined_slab_density hε
  have hp : 0 < (shortDensityExponent σ)+ε := by
    have he := (refined_scale_bounds hσ hσ').2.2.2.2.1
    linarith
  apply zetaDensity_bound_of_eventual_slabs hp hC
  filter_upwards [hslab] with H hh
  exact hh σ hσ hσ'

theorem refined_density_middle {σ ε : ℝ}
    (hσ : 9/13 ≤ σ) (hσ' : σ ≤ 3/4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(18*(1-σ)/(7*σ+3)+ε) := by
  by_cases hs : σ ≤ 5/7
  · exact short_density hσ hs hε
  · exact refined_density (by linarith) hσ' hε

theorem refined_endpoint : shortDensityExponent (3/4) = 6/11 ∧
    (9/16:ℝ)-6/11 = 3/176 := by
  norm_num [shortDensityExponent]

theorem refined_strict_improvement {σ : ℝ} (hσ : 5/7 < σ) (hσ' : σ ≤ 3/4) :
    shortDensityExponent σ < (9/4)*(1-σ) := by
  have hd : 0 < 7*σ+3 := by linarith
  unfold shortDensityExponent
  apply (div_lt_iff₀ hd).mpr
  nlinarith [mul_pos (show 0 < 7*σ-5 by linarith) (show 0 < 1-σ by linarith)]

end Montgomery.Refined

#check Montgomery.Refined.refined_density
#print axioms Montgomery.Refined.refined_density
#print axioms Montgomery.Refined.refined_slab_density
#print axioms Montgomery.Refined.refined_large_values
#print axioms Montgomery.Refined.refined_powered_cover
#print axioms Montgomery.Refined.refined_endpoint
#print axioms Montgomery.Refined.refined_density_middle
