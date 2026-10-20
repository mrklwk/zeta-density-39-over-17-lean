module
public import GeneralCenteredReflection

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

/-- The full discrete centered energy; near-diagonal terms and shell-count
losses have been discharged. Fixed reflected-length factors are absorbed
in the constant; the exact undilated length T/L governs the hypothesis. -/
theorem centered_energy_general (w : MathCollab.Density.ReflectionCutoff)
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 1 < T → 1 ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel w L (t-u)‖^2) ≤
        C*T^η*adjacentCenteredBudget K T L W.card := by
  have hδ : 0 < η/2 := by positivity
  obtain ⟨C,B,hC,hB,hshell⟩ := centered_shell_general w hK (A := 2) (by norm_num) hδ
  obtain ⟨B₀,hB₀,hnear⟩ := GuthMaynard.Improvement.centeredKernel_near w (A := 2) (by norm_num)
  let D : ℝ := 4+1/((η/2)*Real.log 2)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1+B₀^2+D*(C+B),by positivity,?_⟩
  intro T t₀ L hT hL W hW hsep
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := by linarith
  let Y : ℝ := Real.pi*L/8
  have hYp : 0 < Y := by dsimp [Y]; positivity
  have hd1 : 1 ≤ T^(η/2) := Real.one_le_rpow hT.le hδ.le
  have hη1 : 1 ≤ T^η := Real.one_le_rpow hT.le hη.le
  have hpow : T^(η/2)*T^(η/2)=T^η := by
    rw [← Real.rpow_add hTp]
    congr 1
    ring
  have hdist (t : ℝ) (ht : t ∈ W) (u : ℝ) (hu : u ∈ W) : |t-u| ≤ T := by
    obtain ⟨ht1,ht2⟩ := hW t ht
    obtain ⟨hu1,hu2⟩ := hW u hu
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hn (v : ℝ) (hv : |v| ≤ Y) : ‖MathCollab.Density.hKernel w L v‖^2 ≤ B₀^2 := by
    have hh := hnear L v hLp hv
    rw [GuthMaynard.Improvement.centeredKernel_eq_density_hKernel w hLp] at hh
    have hfrac : B₀*L/L^2 ≤ B₀ := by
      have he : B₀*L/L^2=B₀/L := by field_simp
      rw [he]
      exact (div_le_iff₀ hLp).mpr (by nlinarith)
    exact pow_le_pow_left₀ (norm_nonneg _) (hh.trans hfrac) 2
  have hnearSum : (∑ p ∈ (W ×ˢ W).filter (fun p => |p.1-p.2| < Y),
      ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2) ≤ B₀^2*(W.card:ℝ)^2 := by
    calc
      _ ≤ ∑ _p ∈ (W ×ˢ W).filter (fun p => |p.1-p.2| < Y), B₀^2 :=
        sum_le_sum (fun p hp => hn _ (mem_filter.mp hp).2.le)
      _ ≤ ∑ _p ∈ W ×ˢ W, B₀^2 := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = _ := by simp [card_product]; ring
  have hX : 0 ≤ adjacentCenteredBudget K T L W.card :=
    adjacentCenteredBudget_nonneg K (by linarith) (by linarith) (Nat.cast_nonneg _)
  have hfirst := adjacentCenteredBudget_first K (R:=(W.card:ℝ)) (by linarith : 0 ≤ T) (by linarith : 0 ≤ L) (Nat.cast_nonneg _)
  have hbase : B₀^2*(W.card:ℝ)^2 ≤ B₀^2*T^η*adjacentCenteredBudget K T L W.card := by
    have hLR : (W.card:ℝ)^2 ≤ L*(W.card:ℝ)^2 := by nlinarith [sq_nonneg (W.card:ℝ)]
    have hh : (W.card:ℝ)^2 ≤ adjacentCenteredBudget K T L W.card := hLR.trans hfirst
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg B₀)
    have hh'' := mul_le_mul_of_nonneg_left hη1 (mul_nonneg (sq_nonneg B₀) hX)
    nlinarith
  by_cases hYT : Y ≤ T
  · obtain ⟨J,hcover,hmin,hJ⟩ := reflection_shell_count hT hL hYT
    have hfilter : (W ×ˢ W).filter (fun p => |p.1-p.2| < (2:ℝ)^J*Y) = W ×ˢ W := by
      apply filter_eq_self.mpr
      intro p hp
      exact (hdist p.1 (mem_product.mp hp).1 p.2 (mem_product.mp hp).2).trans_lt hcover
    have he := strict_dyadic_prefix (W ×ˢ W) (fun p => |p.1-p.2|)
      (fun p => ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2) hYp.le J
    rw [hfilter] at he
    have hs (j : ℕ) (hj : j ∈ range J) :
        (∑ p ∈ (W ×ˢ W).filter
          (fun p => (2:ℝ)^j*Y ≤ |p.1-p.2| ∧ |p.1-p.2| < (2:ℝ)^(j+1)*Y),
          ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2) ≤
        (C+B)*T^(η/2)*adjacentCenteredBudget K T L W.card := by
      let H := (2:ℝ)^j*Y
      have hHp : 0 < H := by dsimp [H]; positivity
      have hHT : H < 2*T := hmin j (mem_range.mp hj)
      have hh := hshell T t₀ L H hT hL hHp hHT.le W hW hsep
      have her : L^(2-2*(2:ℝ)) ≤ L := by
        simpa using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (2:ℝ)-2*2 ≤ 1)
      have heq : (∑ p ∈ (W ×ˢ W).filter
          (fun p => (2:ℝ)^j*Y ≤ |p.1-p.2| ∧ |p.1-p.2| < (2:ℝ)^(j+1)*Y),
          ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2) =
          MathCollab.Density.shellEnergy w L H W := by
        simp only [sum_filter,sum_product,MathCollab.Density.shellEnergy,H,pow_succ]
        congr 1
        funext t
        congr 1
        funext u
        congr 3; ring
      rw [heq]
      calc
        _ ≤ C*T^(η/2)*adjacentCenteredBudget K T L W.card+B*(W.card:ℝ)^2*L^(2-2*(2:ℝ)) := hh
        _ ≤ C*T^(η/2)*adjacentCenteredBudget K T L W.card+B*(W.card:ℝ)^2*L := by gcongr
        _ = C*T^(η/2)*adjacentCenteredBudget K T L W.card+B*(L*(W.card:ℝ)^2) := by ring
        _ ≤ C*T^(η/2)*adjacentCenteredBudget K T L W.card+B*adjacentCenteredBudget K T L W.card := by gcongr
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd1 (mul_nonneg hB hX)]
    have hJD : (J:ℝ) ≤ D*T^(η/2) := by
      calc
        _ ≤ 4+Real.log T/Real.log 2 := hJ
        _ ≤ 4*T^(η/2)+(T^(η/2)/(η/2))/Real.log 2 := by
          apply add_le_add (by linarith)
          exact div_le_div_of_nonneg_right (Real.log_le_rpow_div hTp.le hδ) htwo.le
        _ = _ := by dsimp [D]; field_simp
    calc
      _ = ∑ p ∈ W ×ˢ W, ‖MathCollab.Density.hKernel w L (p.1-p.2)‖^2 := (sum_product _ _ _).symm
      _ = _ := he
      _ ≤ B₀^2*(W.card:ℝ)^2+∑ _j ∈ range J, (C+B)*T^(η/2)*adjacentCenteredBudget K T L W.card :=
        add_le_add hnearSum (sum_le_sum hs)
      _ = B₀^2*(W.card:ℝ)^2+(J:ℝ)*((C+B)*T^(η/2)*adjacentCenteredBudget K T L W.card) := by simp
      _ ≤ B₀^2*T^η*adjacentCenteredBudget K T L W.card+(D*T^(η/2))*((C+B)*T^(η/2)*adjacentCenteredBudget K T L W.card) := by gcongr
      _ = (B₀^2+D*(C+B))*T^η*adjacentCenteredBudget K T L W.card := by rw [← hpow]; ring
      _ ≤ _ := by gcongr; linarith
  · have hfull : (∑ t ∈ W, ∑ u ∈ W, ‖MathCollab.Density.hKernel w L (t-u)‖^2) ≤
        B₀^2*(W.card:ℝ)^2 := by
      calc
        _ ≤ ∑ _t ∈ W, ∑ _u ∈ W, B₀^2 := by
          apply sum_le_sum
          intro t ht
          apply sum_le_sum
          intro u hu
          exact hn _ ((hdist t ht u hu).trans (le_of_not_ge hYT))
        _ = _ := by simp; ring
    exact hfull.trans (hbase.trans (by gcongr; nlinarith))

/-- The actual squared-cutoff centered matrix satisfies the improved
quadratic trace bound, with no analytic estimate among the premises. -/
theorem centered_trace_general (w : MathCollab.Density.ReflectionCutoff)
    {K : ℕ} (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L : ℝ, 1 < T → 1 ≤ L → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖Matrix.trace (cutoffCenteredMatrix w L W*cutoffCenteredMatrix w L W)‖ ≤
        C*T^η*adjacentCenteredBudget K T L W.card := by
  obtain ⟨C,hC,hbound⟩ := centered_energy_general (reflectionSquare w) hK hη
  refine ⟨C,hC,?_⟩
  intro T t₀ L hT hL W hW hsep
  rw [cutoff_centered_trace_identity,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)))]
  exact hbound T t₀ L hT hL W hW hsep

end Montgomery.RationalMoment
