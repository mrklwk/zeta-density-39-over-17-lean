import GuthMaynard.Improvement.SourceSpectralRaw
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- The raw amplifier loss is uniformly absorbed on polynomial scale ranges. -/
theorem spectral_prefactor_budget {δ η ε A p P N L : ℝ}
    (hη : 0 < η) (hA : 1 ≤ A) (hp : 0 < p)
    (hP : 0 < P) (hN : 2 ≤ N) (hL : N ≤ L) (hLA : L ≤ A*N^p)
    (hexp : 3*p*η+ε ≤ δ) :
    4*(P*(1+L)^η*(N+1))^3*N^ε ≤
      (32*P^3*((1+A)^η)^3)*N^δ*N^3 := by
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hNp : 1 ≤ N^p := Real.one_le_rpow hN1 hp.le
  have hbase : 1+L ≤ (1+A)*N^p := by nlinarith
  have hpow : (1+L)^η ≤ (1+A)^η*N^(p*η) := by
    calc
      _ ≤ ((1+A)*N^p)^η := Real.rpow_le_rpow (by linarith) hbase hη.le
      _ = _ := by rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hN0.le _),
        ← Real.rpow_mul hN0.le]
  have hc : 4*(P*(1+L)^η*(N+1))^3*N^ε ≤
      4*(P*((1+A)^η*N^(p*η))*(2*N))^3*N^ε := by
    gcongr
    first | positivity | exact hpow | linarith
  have he : (N^(p*η))^3*N^ε ≤ N^δ := by
    rw [← Real.rpow_natCast (N^(p*η)) 3, ← Real.rpow_mul hN0.le,
      ← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    norm_num only [Nat.cast_ofNat]
    nlinarith
  calc
    _ ≤ 4*(P*((1+A)^η*N^(p*η))*(2*N))^3*N^ε := hc
    _ = (32*P^3*((1+A)^η)^3)*((N^(p*η))^3*N^ε)*N^3 := by ring
    _ ≤ _ := by gcongr

/-- Scalar expansion keeps all three homogeneous terms and no analytic premise. -/
theorem spectral_raw_scale_budget {δ η ε A p P D R N L T B M X : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (hA : 1 ≤ A) (hp : 0 < p)
    (hP : 0 < P) (hD : 0 < D) (hR : 0 < R)
    (hN : 2 ≤ N) (hL : N ≤ L) (hLA : L ≤ A*N^p)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hM : 0 ≤ M) (hX : 0 ≤ X)
    (hexp : 3*p*η+ε ≤ δ) :
    4*(P*(1+L)^η*(N+1))^3*
      ((D*L*B)^3+(2*N/L)*(X+R*N^ε*L^2*N*T*M)) ≤
    (32*P^3*((1+A)^η)^3)*(D^3+2+2*R)*N^δ*
      ((N*L*B)^3+(N^4/L)*X+N^5*L*T*M) := by
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := by linarith
  have he : 1 ≤ N^ε := Real.one_le_rpow (by linarith) hε.le
  have hf := spectral_prefactor_budget hη hA hp hP hN hL hLA hexp
  let K := 32*P^3*((1+A)^η)^3
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hstep : (D*L*B)^3+(2*N/L)*(X+R*N^ε*L^2*N*T*M) ≤
      N^ε*((D*L*B)^3+(2*N/L)*(X+R*L^2*N*T*M)) := by
    have h1 : (D*L*B)^3 ≤ N^ε*(D*L*B)^3 := le_mul_of_one_le_left (by positivity) he
    have h2 : X ≤ N^ε*X := le_mul_of_one_le_left hX he
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2*N/L by positivity)
    nlinarith
  calc
    _ ≤ (4*(P*(1+L)^η*(N+1))^3*N^ε)*
        ((D*L*B)^3+(2*N/L)*(X+R*L^2*N*T*M)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hstep
        (show 0 ≤ 4*(P*(1+L)^η*(N+1))^3 by positivity)
    _ ≤ (K*N^δ*N^3)*((D*L*B)^3+(2*N/L)*(X+R*L^2*N*T*M)) :=
      mul_le_mul_of_nonneg_right hf (by positivity)
    _ = K*N^δ*(D^3*(N*L*B)^3+2*((N^4/L)*X)+2*R*(N^5*L*T*M)) := by
      dsimp [K]
      field_simp
      ring
    _ ≤ _ := by
      have hb : 0 ≤ (N*L*B)^3 := by positivity
      have hx : 0 ≤ (N^4/L)*X := by positivity
      have hm : 0 ≤ N^5*L*T*M := by positivity
      have hi : D^3*(N*L*B)^3+2*((N^4/L)*X)+2*R*(N^5*L*T*M) ≤
          (D^3+2+2*R)*((N*L*B)^3+(N^4/L)*X+N^5*L*T*M) := by
        nlinarith [mul_nonneg (show 0 ≤ D^3 by positivity) hx,
          mul_nonneg (show 0 ≤ D^3 by positivity) hm,
          mul_nonneg hR.le hb, mul_nonneg hR.le hx]
      simpa [K, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hi (show 0 ≤ K*N^δ by positivity)

/-- Actual spectral mass bound with all subpower losses absorbed uniformly.
The cubic is the literal centered kernel integral, not an assumed estimate. -/
theorem source_spectral_scale (w : MathCollab.Density.ComparisonCutoff)
    {δ A p : ℝ} (hδ : 0 < δ) (hA : 1 ≤ A) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N L T t₀ : ℝ,
      2 ≤ N → N ≤ L → L ≤ A*N^p → 0 ≤ T → T ≤ A*N^p →
      ∀ (a : ℕ → ℂ) (μ : ℝ → ℝ),
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) → Measurable μ → Integrable μ →
      Integrable (fun t => μ t^2) → (∀ t, 0 ≤ μ t) →
      Function.support μ ⊆ Icc t₀ (t₀+T) → ∀ B : ℝ, 0 ≤ B →
      (∀ t, μ t ≤ min (‖boundedPolynomial N a t‖^2) B) →
      (∫ t, μ t^2)^3 ≤ C*N^δ*((N*L*B)^3+(N^4/L)*
        ‖kernelCubic (timeMeasure μ)
          (centeredKernel (fun x => ((w x^2:ℝ):ℂ)) (1/2) 5 L)‖+
        N^5*L*T*(∫ t, μ t^2)) := by
  let η := δ/(6*p)
  let ε := δ/2
  have hη : 0 < η := by dsimp [η]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hexp : 3*p*η+ε ≤ δ := by dsimp [η, ε]; field_simp; nlinarith
  obtain ⟨P,D,R,hP,hD,hR,hr⟩ := source_spectral_raw w hη hε hA hp
  refine ⟨(32*P^3*((1+A)^η)^3)*(D^3+2+2*R), by positivity, ?_⟩
  intro N L T t₀ hN hL hLA hT hTA a μ ha hm hi h2 h0 hs B hB hμ
  exact (hr N L T t₀ hN hL hT hTA a μ ha hm hi h2 h0 hs B hB hμ).trans
    (spectral_raw_scale_budget hη hε hA hp hP hD hR hN hL hLA hT hB
      (integral_nonneg (fun t => sq_nonneg (μ t))) (norm_nonneg _) hexp)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.spectral_prefactor_budget
#print axioms GuthMaynard.Improvement.spectral_raw_scale_budget
#print axioms GuthMaynard.Improvement.source_spectral_scale
