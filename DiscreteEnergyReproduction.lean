module
public import CenteredMixedTrace
public import GuthMaynard.Improvement.SourceQuarticKernel

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- A positive integrable kernel with a uniform bound under unit shifts. -/
def energyReproducingWeight (t : ℝ) : ℝ := (1+t^2)⁻¹

theorem energy_weight_nonneg (t : ℝ) : 0 ≤ energyReproducingWeight t := by
  unfold energyReproducingWeight
  positivity

theorem energy_weight_integrable : Integrable energyReproducingWeight :=
  integrable_inv_one_add_sq

theorem energy_weight_shift {x y : ℝ} (hxy : |x-y| ≤ 1) :
    energyReproducingWeight x ≤ 3*energyReproducingWeight y := by
  have hd : (x-y)^2 ≤ 1 := by nlinarith [sq_abs (x-y),abs_nonneg (x-y)]
  have hs : 1+y^2 ≤ 3*(1+x^2) := by nlinarith [sq_nonneg (2*x-y)]
  unfold energyReproducingWeight
  simp only [inv_eq_one_div]
  calc
    _ ≤ 3/(1+y^2) := (div_le_div_iff₀ (by positivity : 0 < 1+x^2)
      (by positivity : 0 < 1+y^2)).mpr (by nlinarith)
    _ = _ := by ring

/-- Every translated weighted square of the actual finite polynomial is integrable. -/
theorem detecting_energy_weight_integrable (N : ℝ) (a : ℕ → ℂ) (s : ℝ) :
    Integrable (fun t => energyReproducingWeight (t-s)*
      ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2) := by
  obtain ⟨hc,hb⟩ := GuthMaynard.Improvement.boundedPolynomial_regular N a
  apply (energy_weight_integrable.comp_sub_right s).mul_bdd (hc.norm.pow 2).aestronglyMeasurable
    (c := (∑ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖)^2)
  filter_upwards with t
  change |‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2| ≤ _
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2

/-- Unit-nearby ordinates in a one-separated set have multiplicity at most three. -/
theorem energy_nearby_card_le (W : Finset ℝ)
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) (s : ℝ) :
    ((W.filter (fun t => |s-t| ≤ 1)).card:ℝ) ≤ 3 := by
  have hh := separated_interval_card (T := 2) (t₀ := s-1) (by norm_num)
    (W.filter (fun t => |s-t| ≤ 1))
    (by
      intro t ht
      have hp := abs_le.mp (mem_filter.mp ht).2
      constructor <;> linarith)
    (by
      intro t ht u hu hne
      exact hsep t (mem_filter.mp ht).1 u (mem_filter.mp hu).1 hne)
  norm_num at hh
  exact_mod_cast hh

/-- The literal quadruple count, including equality at distance one. -/
def discreteAdditiveEnergy (W : Finset ℝ) : ℕ :=
  (((W ×ˢ W) ×ˢ (W ×ˢ W)).filter
    (fun p => |p.1.1+p.1.2-p.2.1-p.2.2| ≤ 1)).card

theorem discrete_energy_fibers (W : Finset ℝ) :
    (discreteAdditiveEnergy W:ℝ) = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ((W.filter (fun t₄ => |t₁+t₂-t₃-t₄| ≤ 1)).card:ℝ) := by
  unfold discreteAdditiveEnergy
  simp only [card_eq_sum_ones,Nat.cast_sum,sum_filter,sum_product]

/-- The existing Schwartz reproducer controls the actual detecting polynomial
at any point, using one fixed positive kernel and one uniform constant. -/
theorem detecting_square_reproduction :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ (a : ℕ → ℂ) (w : ℝ),
      ‖GuthMaynard.Improvement.boundedPolynomial N a w‖^2 ≤
        C*∫ t, energyReproducingWeight (t-w)*
          ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 := by
  open GuthMaynard.Improvement in
  obtain ⟨B,hB,hdec⟩ := source_quartic_weight_decay 2
  open GuthMaynard.Improvement in
  let mass : ℝ := ∫ s, sourceQuarticWeight s
  open GuthMaynard.Improvement in
  have hmass : 0 ≤ mass := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨1+mass*B,by positivity,?_⟩
  intro N hN a w
  open GuthMaynard.Improvement in
  obtain ⟨hc,hb⟩ := boundedPolynomial_regular N a
  open GuthMaynard.Improvement in
  have hi : Integrable (fun t => sourceReproducingKernel (t-w)) :=
    sourceReproducingKernel.integrable.comp_sub_right w
  open GuthMaynard.Improvement in
  have hf := MathCollab.Density.norm_integral_mul_sq_le hi hc.aestronglyMeasurable hb
  open GuthMaynard.Improvement in
  rw [← boundedPolynomial_reproduce hN a w] at hf
  open GuthMaynard.Improvement in
  have hmass_eq : (∫ t, sourceQuarticWeight (t-w)) = mass := integral_sub_right_eq_self _ w
  change ‖GuthMaynard.Improvement.boundedPolynomial N a w‖^2 ≤
    (∫ t, GuthMaynard.Improvement.sourceQuarticWeight (t-w))*
      (∫ t, GuthMaynard.Improvement.sourceQuarticWeight (t-w)*
        ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2) at hf
  rw [hmass_eq] at hf
  have hkernel (x : ℝ) : GuthMaynard.Improvement.sourceQuarticWeight x ≤
      B*energyReproducingWeight x := by
    refine (hdec x).trans ?_
    have hh : 1+x^2 ≤ (1+|x|)^2 := by nlinarith [sq_abs x,abs_nonneg x]
    simpa only [energyReproducingWeight,div_eq_mul_inv] using
      div_le_div_of_nonneg_left hB.le (by positivity : 0 < 1+x^2) hh
  have hweight : Integrable (fun t => energyReproducingWeight (t-w)*
      ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2) := by
    apply (energy_weight_integrable.comp_sub_right w).mul_bdd (hc.norm.pow 2).aestronglyMeasurable
      (c := (∑ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖)^2)
    filter_upwards with t
    change |‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2
  have hint : (∫ t, GuthMaynard.Improvement.sourceQuarticWeight (t-w)*
      ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2) ≤
      B*∫ t, energyReproducingWeight (t-w)*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae
    · exact GuthMaynard.Improvement.source_quartic_weighted_integrable N a w 2
    · convert hweight.const_mul B using 1

    · filter_upwards with t
      nlinarith [mul_le_mul_of_nonneg_right (hkernel (t-w))
        (sq_nonneg ‖GuthMaynard.Improvement.boundedPolynomial N a t‖)]
  exact hf.trans ((mul_le_mul_of_nonneg_left hint hmass).trans (by
    have h0 : 0 ≤ ∫ t, energyReproducingWeight (t-w)*
        ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 := integral_nonneg (fun t => mul_nonneg (energy_weight_nonneg _) (sq_nonneg _))
    nlinarith))

/-- The positive triple convolution used by the discrete energy argument. -/
def energyTripleWeight (W : Finset ℝ) (t : ℝ) : ℝ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
    energyReproducingWeight (t-(t₁+t₂-t₃))

theorem energy_triple_weight_integrable (W : Finset ℝ) : Integrable (energyTripleWeight W) :=
  integrable_finsetSum _ (fun _ _ => integrable_finsetSum _ (fun _ _ =>
    integrable_finsetSum _ (fun _ _ => energy_weight_integrable.comp_sub_right _)))

open scoped FourierTransform in
/-- Exact triple Fourier factorization; no small-gcd estimate is assumed. -/
theorem energy_triple_fourier (W : Finset ℝ) (ξ : ℝ) :
    𝓕 (fun t => (energyTripleWeight W t:ℂ)) ξ =
      ((∑ t ∈ W, GuthMaynard.Improvement.phase (-ξ*t))^2 *
        star (∑ t ∈ W, GuthMaynard.Improvement.phase (-ξ*t))) *
        𝓕 (fun t => (energyReproducingWeight t:ℂ)) ξ := by
  let κ : ℝ → ℂ := fun t => (energyReproducingWeight t:ℂ)
  have hi (s : ℝ) : Integrable (fun t => GuthMaynard.Improvement.phase (-ξ*t)*κ (t-s)) :=
    GuthMaynard.Improvement.integrable_phase_mul (energy_weight_integrable.ofReal.comp_sub_right s) ξ
  have ht (s : ℝ) : (∫ t, GuthMaynard.Improvement.phase (-ξ*t)*κ (t-s)) =
      GuthMaynard.Improvement.phase (-ξ*s)*𝓕 κ ξ := by
    have hh := GuthMaynard.Improvement.source_kernel_phase_integral κ (-ξ) s
    convert hh using 1
    · apply integral_congr_ae
      filter_upwards with t
      ring
    · simp only [neg_neg]
      congr 1
      ring
  have hp (a b c : ℝ) : GuthMaynard.Improvement.phase (-ξ*(a+b-c)) =
      GuthMaynard.Improvement.phase (-ξ*a)*GuthMaynard.Improvement.phase (-ξ*b)*
        star (GuthMaynard.Improvement.phase (-ξ*c)) := by
    change _ = _ * _ * (starRingEnd ℂ) _
    rw [GuthMaynard.Improvement.operator_phase_conj,← GuthMaynard.Improvement.phase_add,
      ← GuthMaynard.Improvement.phase_add]
    congr 1
    ring
  rw [GuthMaynard.Improvement.fourier_eq_phase_integral]
  simp_rw [energyTripleWeight,Complex.ofReal_sum,mul_sum]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    integrable_finsetSum _ (fun c _ => hi (a+b-c))))]
  simp_rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => hi (_+b-c))),
    integral_finsetSum _ (fun c _ => hi (_+_-c)),ht,hp]
  simp only [pow_two,star_sum,sum_mul,mul_sum]
  have hs (f : ℝ → ℝ → ℝ → ℂ) :
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, f a b c) =
        ∑ c ∈ W, ∑ a ∈ W, ∑ b ∈ W, f a b c := by
    calc
      _ = ∑ a ∈ W, ∑ c ∈ W, ∑ b ∈ W, f a b c :=
        sum_congr rfl (fun a _ => sum_comm)
      _ = _ := sum_comm
  rw [hs]
  dsimp only [κ]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro c _
  ring

open scoped FourierTransform in
/-- The triple convolution gives exactly the cubic rational phase sum. -/
theorem energy_triple_fourier_norm (W : Finset ℝ) (r : ℝ) :
    ‖𝓕 (fun t => (energyTripleWeight W t:ℂ)) (Real.log r/(2*Real.pi))‖ ≤
      (∫ t, energyReproducingWeight t)*‖∑ t ∈ W, phase r t‖^3 := by
  rw [energy_triple_fourier,norm_mul,norm_mul,norm_pow,norm_star]
  have he (t : ℝ) : GuthMaynard.Improvement.phase (-(Real.log r/(2*Real.pi))*t) =
      star (phase r t) := by
    rw [show -(Real.log r/(2*Real.pi))*t = (-t)*GuthMaynard.Improvement.mellinFrequency r by
      unfold GuthMaynard.Improvement.mellinFrequency; ring,
      GuthMaynard.Improvement.mellinFrequency_phase]
    change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring
  simp_rw [he,← star_sum,norm_star]
  have hf := GuthMaynard.Improvement.time_fourier_norm_le_mass
    (μ := energyReproducingWeight) (by unfold energyReproducingWeight; fun_prop)
    energy_weight_nonneg energy_weight_integrable (Real.log r/(2*Real.pi))

  nlinarith [mul_le_mul_of_nonneg_right hf (pow_nonneg (norm_nonneg (∑ t ∈ W, phase r t)) 3)]

/-- A unit displacement changes only the universal reproducing constant. -/
theorem detecting_near_square_reproduction :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ (a : ℕ → ℂ) (s w : ℝ),
      |s-w| ≤ 1 → ‖GuthMaynard.Improvement.boundedPolynomial N a w‖^2 ≤
        C*∫ t, energyReproducingWeight (t-s)*
          ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 := by
  obtain ⟨C,hC,hrepro⟩ := detecting_square_reproduction
  refine ⟨3*C,by positivity,?_⟩
  intro N hN a s w hsw
  have hi : (∫ t, energyReproducingWeight (t-w)*
      ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2) ≤
      3*∫ t, energyReproducingWeight (t-s)*
        ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae (detecting_energy_weight_integrable N a w)
      ((detecting_energy_weight_integrable N a s).const_mul 3)
    filter_upwards with t
    have hh := energy_weight_shift (x := t-w) (y := t-s) (by
      convert hsw using 1; ring)
    nlinarith [mul_le_mul_of_nonneg_right hh
      (sq_nonneg ‖GuthMaynard.Improvement.boundedPolynomial N a t‖)]
  exact (hrepro N hN a w).trans ((mul_le_mul_of_nonneg_left hi hC.le).trans_eq (by ring))

/-- Actual large values and one-separation yield a lower bound for the
positive triple convolution, with the exact discrete quadruple count. -/
theorem discrete_energy_reproduction_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
      0 ≤ V → (∀ t ∈ W, V ≤ ‖GuthMaynard.Improvement.boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (discreteAdditiveEnergy W:ℝ)*V^2 ≤
        C*∫ t, energyTripleWeight W t*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 := by
  obtain ⟨C,hC,hrepro⟩ := detecting_near_square_reproduction
  refine ⟨3*C,by positivity,?_⟩
  intro N hN a W V hV hlarge hsep
  have hi (s : ℝ) := detecting_energy_weight_integrable N a s
  have hnonneg (s : ℝ) : 0 ≤ ∫ t, energyReproducingWeight (t-s)*
      ‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 :=
    integral_nonneg (fun t => mul_nonneg (energy_weight_nonneg _) (sq_nonneg _))
  have hf (s : ℝ) : ((W.filter (fun w => |s-w| ≤ 1)).card:ℝ)*V^2 ≤
      3*C*∫ t, energyReproducingWeight (t-s)*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 := by
    calc
      _ = ∑ _w ∈ W.filter (fun w => |s-w| ≤ 1), V^2 := by simp
      _ ≤ ∑ _w ∈ W.filter (fun w => |s-w| ≤ 1),
          C*∫ t, energyReproducingWeight (t-s)*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 := by
        apply sum_le_sum
        intro w hw
        exact (pow_le_pow_left₀ hV (hlarge w (mem_filter.mp hw).1) 2).trans
          (hrepro N hN a s w (mem_filter.mp hw).2)
      _ = ((W.filter (fun w => |s-w| ≤ 1)).card:ℝ)*
          (C*∫ t, energyReproducingWeight (t-s)*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2) := by simp
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right (energy_nearby_card_le W hsep s)
          (mul_nonneg hC.le (hnonneg s))
        nlinarith
  have he : (∫ t, energyTripleWeight W t*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2) =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ∫ t, energyReproducingWeight (t-(t₁+t₂-t₃))*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2 := by
    simp only [energyTripleWeight,sum_mul]
    rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
      integrable_finsetSum _ (fun z _ => hi (x+y-z))))]
    apply sum_congr rfl
    intro x _
    rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _ (fun z _ => hi (x+y-z)))]
    apply sum_congr rfl
    intro y _
    exact integral_finsetSum _ (fun z _ => hi (x+y-z))
  rw [discrete_energy_fibers,he]
  simp only [sum_mul,mul_sum]
  exact sum_le_sum (fun x _ => sum_le_sum (fun y _ => sum_le_sum (fun z _ => hf (x+y-z))))

/-- The triple-convolution upper bound is the actual cubic rational sum. -/
theorem discrete_energy_triple_upper {N : ℝ} (hN : 0 < N) (a : ℕ → ℂ)
    (ha : ∀ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖ ≤ 1) (W : Finset ℝ) :
    (∫ t, energyTripleWeight W t*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2) ≤
      (∫ t, energyReproducingWeight t)*
        (∑ n ∈ GuthMaynard.Improvement.sourceRatioIndices N,
          ∑ m ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖∑ t ∈ W, phase ((n:ℝ)/m) t‖^3) := by
  let E : ℝ := ∫ t, energyTripleWeight W t*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2
  have hE : 0 ≤ E := integral_nonneg (fun t => mul_nonneg
    (sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => energy_weight_nonneg _)))) (sq_nonneg _))
  have hh := GuthMaynard.Improvement.boundedPolynomial_pairing_ratio_bound hN a ha
    (energy_triple_weight_integrable W).ofReal
  simp only [← Complex.ofReal_pow] at hh
  have he : (∫ t, ((‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2:ℝ):ℂ)*
      (energyTripleWeight W t:ℂ)) = (E:ℂ) := by
    calc
      _ = ∫ t, ((energyTripleWeight W t*‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2:ℝ):ℂ) := by
        apply integral_congr_ae
        filter_upwards with t
        push_cast
        ring
      _ = (E:ℂ) := integral_ofReal
  have hh' : E ≤ ∑ n ∈ GuthMaynard.Improvement.sourceRatioIndices N,
      ∑ m ∈ GuthMaynard.Improvement.sourceRatioIndices N,
        ‖FourierTransform.fourier (fun t => (energyTripleWeight W t:ℂ)) (Real.log ((n:ℝ)/m)/(2*Real.pi))‖ := by
    calc
      E = ‖(E:ℂ)‖ := by simp [Real.norm_eq_abs,abs_of_nonneg hE]
      _ = ‖∫ t, ((‖GuthMaynard.Improvement.boundedPolynomial N a t‖^2:ℝ):ℂ)*
          (energyTripleWeight W t:ℂ)‖ := congrArg norm he.symm
      _ ≤ _ := hh
  exact hh'.trans (by
    rw [mul_sum]
    apply sum_le_sum
    intro n _
    rw [mul_sum]
    exact sum_le_sum (fun m _ => energy_triple_fourier_norm W ((n:ℝ)/m)))

/-- The missing discrete reproducing-kernel bridge is unconditional:
large values on a one-separated set control its literal additive energy
by the cubic rational-frequency sum. Constants are uniform in every scale. -/
theorem discrete_additive_energy_reproducing :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
      (∀ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖ ≤ 1) →
      0 ≤ V → (∀ t ∈ W, V ≤ ‖GuthMaynard.Improvement.boundedPolynomial N a t‖) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (discreteAdditiveEnergy W:ℝ)*V^2 ≤ C*
        (∑ n ∈ GuthMaynard.Improvement.sourceRatioIndices N,
          ∑ m ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖∑ t ∈ W, phase ((n:ℝ)/m) t‖^3) := by
  obtain ⟨C,hC,hlower⟩ := discrete_energy_reproduction_lower
  have hmass : 0 ≤ ∫ t, energyReproducingWeight t := integral_nonneg energy_weight_nonneg
  refine ⟨C*(1+∫ t, energyReproducingWeight t),by positivity,?_⟩
  intro N hN a W V ha hV hlarge hsep
  have hh := hlower N hN a W V hV hlarge hsep
  have hu := discrete_energy_triple_upper hN a ha W
  exact hh.trans ((mul_le_mul_of_nonneg_left hu hC.le).trans (by
    have h0 : 0 ≤ ∑ n ∈ GuthMaynard.Improvement.sourceRatioIndices N,
        ∑ m ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖∑ t ∈ W, phase ((n:ℝ)/m) t‖^3 := by positivity
    nlinarith))

end Montgomery.RationalMoment
