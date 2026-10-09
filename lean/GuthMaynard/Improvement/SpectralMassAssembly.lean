import GuthMaynard.Improvement.AmplifierQuantitative
import GuthMaynard.Improvement.OperatorNuclearSpectral
import GuthMaynard.Improvement.OperatorSchur
import GuthMaynard.Improvement.SourceDirichletPairing
set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped InnerProductSpace ContDiff
namespace GuthMaynard.Improvement

/-- The original polynomial is globally bounded, so ordinary L1 of mu
supplies integrability of its actual weighted square. -/
theorem spectral_weighted_polynomial_integrable (N : ℝ) (a : ℕ → ℂ)
    {μ : ℝ → ℝ} (hi : Integrable μ) :
    Integrable (fun t => μ t*‖boundedPolynomial N a t‖^2) := by
  obtain ⟨hc,hb⟩ := boundedPolynomial_regular N a
  apply hi.mul_bdd (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr (hb t)

/-- The genuine fourth-moment mass is below the actual amplifier column
mass, from the pointwise density domination, with both integrals justified. -/
theorem spectral_mass_le_polynomial_mass (N : ℝ) (a : ℕ → ℂ)
    {μ : ℝ → ℝ} (hi : Integrable μ) (h2 : Integrable (fun t => μ t^2))
    (h0 : ∀ t, 0 ≤ μ t) (hD : ∀ t, μ t ≤ ‖boundedPolynomial N a t‖^2) :
    (∫ t, μ t^2) ≤ ∫ t, μ t*‖boundedPolynomial N a t‖^2 := by
  apply integral_mono h2 (spectral_weighted_polynomial_integrable N a hi)
  intro t
  simpa only [pow_two] using mul_le_mul_of_nonneg_left (hD t) (h0 t)

/-- Elementary conversion of the positive-part spectral bound, retaining
all divisor and cardinality factors explicitly. -/
theorem spectral_mass_scalar {M P S k Z : ℝ} (hM : 0 ≤ M) (hP : 0 < P)
    (hS : 0 ≤ S) (hk : 0 < k) (h : k*(max (M/P-S) 0)^3 ≤ Z) :
    M^3 ≤ 4*P^3*(S^3+Z/k) := by
  let z := max (M/P-S) 0
  have hz : 0 ≤ z := le_max_right _ _
  have hx : M/P ≤ S+z := by dsimp [z]; linarith [le_max_left (M/P-S) 0]
  have hpow : (M/P)^3 ≤ (S+z)^3 := pow_le_pow_left₀ (div_nonneg hM hP.le) hx 3
  have hfour : (S+z)^3 ≤ 4*(S^3+z^3) := by
    nlinarith [mul_nonneg (sq_nonneg (S-z)) (add_nonneg hS hz)]
  have ht : z^3 ≤ Z/k := (le_div_iff₀ hk).mpr (by simpa only [mul_comm,z] using h)
  have hall : (M/P)^3 ≤ 4*(S^3+Z/k) := hpow.trans (hfour.trans (by linarith))
  have hm := mul_le_mul_of_nonneg_left hall (pow_nonneg hP.le 3)
  have he : P^3*(M/P)^3=M^3 := by rw [← mul_pow,mul_div_cancel₀ _ hP.ne']
  rw [he] at hm
  nlinarith

set_option maxHeartbeats 2400000 in
/-- Quantitative actual spectral comparison with the amplifier and Schur
premises discharged. Only the displayed actual mixed trace bound remains.
The cubic term is the literal centered time kernel, not an abstract bound. -/
theorem actual_spectral_mass_bound {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    {l u : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) (hu4 : 4 ≤ u)
    (hplateau : ∀ x ∈ Icc (1:ℝ) 4, w x=1)
    (hs : ∀ x, x ∉ Icc l u → w x=0) {η : ℝ} (hη : 0 < η) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      ∀ (N L : ℝ), 0 < N → N ≤ L → ∀ (a : ℕ → ℂ),
      (∀ n ∈ amplifierSource N, ‖a n‖ ≤ 1) →
      ∀ (μ : ℝ → ℝ), Measurable μ → (hiμ : Integrable μ) →
      Integrable (fun t => μ t^2) → (∀ t, 0 ≤ μ t) →
      ∀ B : ℝ, 0 ≤ B → (∀ t, μ t ≤ min (‖boundedPolynomial N a t‖^2) B) →
      let _ : IsFiniteMeasure (timeMeasure μ) := timeMeasure_finite hiμ
      ∀ (ι : Type) [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 (timeMeasure μ))) (Q : ℝ),
      (operatorDiagonalTrace b
        (operatorContinuous (timeMeasure μ) (fun x => w x^2) L *
          (operatorDiscrete (timeMeasure μ) (fun x => w x^2) L l u -
            operatorContinuous (timeMeasure μ) (fun x => w x^2) L)^2)).re ≤ Q →
      (L/(2*N))*(max ((∫ t, μ t^2)/(A*(1+L)^η*(N+1))-D*L*B) 0)^3 ≤
        ‖kernelCubic (timeMeasure μ) (centeredKernel (fun x => ((w x^2:ℝ):ℂ)) l u L)‖+Q ∧
      (∫ t, μ t^2)^3 ≤ 4*(A*(1+L)^η*(N+1))^3*
        ((D*L*B)^3+(2*N/L)*
          (‖kernelCubic (timeMeasure μ) (centeredKernel (fun x => ((w x^2:ℝ):ℂ)) l u L)‖+Q)) := by
  let cutoff := fun x => w x^2
  have hc : Continuous cutoff := hw.continuous.pow 2
  have hc0 (x : ℝ) : 0 ≤ cutoff x := sq_nonneg _
  have hcs (x : ℝ) (hx : x ∉ Icc l u) : cutoff x=0 := by simp [cutoff,hs x hx]
  have hlu : l ≤ u := by linarith
  have hci : Integrable cutoff := hc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hcs)
  obtain ⟨W,hW⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  let W' := max 0 W
  have hW0 : 0 ≤ W' := le_max_left _ _
  have hcW (x : ℝ) : |cutoff x| ≤ W' := by
    by_cases hx : x ∈ Icc l u
    · exact (hW x hx).trans (le_max_right _ _)
    · rw [hcs x hx,abs_zero]; exact hW0
  obtain ⟨A,hA,hamp⟩ := amplifier_time_density_witness hη
  obtain ⟨D,hD,hschur⟩ := operator_fixed_cutoff_schur hc hc0 hl hlu hcs
  refine ⟨A,D,hA,hD,?_⟩
  intro N L hN hNL a ha μ hm hiμ h2 h0 B hB hμ
  let _ : IsFiniteMeasure (timeMeasure μ) := timeMeasure_finite hiμ
  dsimp only
  intro ι _ b Q hQ
  have hL : 0 < L := hN.trans_le hNL
  have hP : 0 < A*(1+L)^η*(N+1) := by positivity
  have hμB (t : ℝ) : μ t ≤ B := (hμ t).trans (min_le_right _ _)
  have hμD (t : ℝ) : μ t ≤ ‖boundedPolynomial N a t‖^2 := (hμ t).trans (min_le_left _ _)
  obtain ⟨r,hr,v,hv,hwit⟩ := hamp N L l u hN hNL hl1 hu4 a w ha hplateau μ hm hiμ h0
  have hmass := spectral_mass_le_polynomial_mass N a hiμ h2 h0 hμD
  have hwit' : ((amplifierColumns N L).card:ℝ)*((∫ t, μ t^2)/(A*(1+L)^η*(N+1))) ≤
      ∑ j, (inner ℂ (v j) (operatorDiscrete (timeMeasure μ) cutoff L l u (v j))).re :=
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmass hP.le) (Nat.cast_nonneg _)).trans hwit
  have hC := hschur μ hm hiμ h0 B hB hμB L hL.le
  have hspec := operator_centered_spectral_comparison (timeMeasure μ) hc.measurable hci hc0
    hl hL hW0 hcW hcs b v hv (by simpa using (show (r:ℝ) ≤ (amplifierColumns N L).card by exact_mod_cast hr)) hC hwit'
  rw [operator_centered_cubic (timeMeasure μ) hc.measurable hci hl hL hW0 hcW hcs b] at hspec
  have hgate : (L/(2*N))*(max ((∫ t, μ t^2)/(A*(1+L)^η*(N+1))-D*L*B) 0)^3 ≤
      ‖kernelCubic (timeMeasure μ) (centeredKernel (fun x => ((w x^2:ℝ):ℂ)) l u L)‖+Q := by
    have hk : L/(2*N) ≤ ((amplifierColumns N L).card:ℝ) := by
      convert (amplifier_columns_card hN hNL).1 using 1
      ring
    exact (mul_le_mul_of_nonneg_right hk (pow_nonneg (le_max_right _ _) 3)).trans
      (hspec.trans (add_le_add le_rfl hQ))
  refine ⟨hgate,?_⟩
  have hfinal := spectral_mass_scalar (integral_nonneg (fun t => sq_nonneg (μ t))) hP
    (show 0 ≤ D*L*B by positivity) (show 0 < L/(2*N) by positivity) hgate
  have he (Z : ℝ) : Z/(L/(2*N))=(2*N/L)*Z := by field_simp
  simpa only [he] using hfinal

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.spectral_weighted_polynomial_integrable
#print axioms GuthMaynard.Improvement.spectral_mass_le_polynomial_mass
#print axioms GuthMaynard.Improvement.spectral_mass_scalar
#print axioms GuthMaynard.Improvement.actual_spectral_mass_bound
