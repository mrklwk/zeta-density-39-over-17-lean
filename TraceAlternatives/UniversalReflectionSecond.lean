module
public import TraceAlternatives.UniversalProfileScaling
public import TraceAlternatives.CubeReflectionSecond

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

theorem ratio_second_universal_uniform_translate (ε B : ℝ)
    (hε : 0<ε) (_hB : 0<B) :
    ∃ C : ℝ, 0<C ∧ ∀ T t₀ : ℝ, 2≤T → ∀ M : ℕ,
      0<M → (M:ℝ)^2≤B*T → ∀ W : Finset ℝ,
      (∀ t∈W,t∈Set.Icc t₀ (t₀+T)) →
      finiteRatioSecond (Ioc M (2*M)) W ≤
        C*T^ε*universalShortProfile T M W.card (discreteAdditiveEnergy W) := by
  obtain ⟨C,hC,hBound⟩ := actual_second_moment_universal_native ε hε
  let D : ℝ := max 1 B
  have hD1 : 1≤D := le_max_left _ _
  have hBD : B≤D := le_max_right _ _
  have hD : 0<D := by linarith
  refine ⟨C*D^ε*D^3,by positivity,?_⟩
  intro T t₀ hT M hM hMT W hW
  have hTp : 0<T := by linarith
  have hDT : T≤D*T := le_mul_of_one_le_left hTp.le hD1
  have hBase : InBaseInterval (D*T) (translateSet t₀ W) := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
    obtain ⟨hl,hh⟩ := hW u hu
    exact ⟨by linarith,by linarith⟩
  have h := hBound M (D*T) (fun _ => 1) (translateSet t₀ W) hM
    (hT.trans hDT) (hMT.trans (by gcongr)) (by intro n hn; norm_num) hBase
  rw [coefficient_one_difference_eq_ratio_second,← finiteRatioSecond_dyadic,
    finiteRatioSecond_translateSet _ (fun n hn => by have := (mem_Ioc.mp hn).1; omega),
    translateSet_card,discrete_energy_translateSet,Real.mul_rpow hD.le hTp.le] at h
  have hScale : universalShortProfile (D*T) M W.card (discreteAdditiveEnergy W) ≤
      D^3*universalShortProfile T M W.card (discreteAdditiveEnergy W) := by
    exact (universalShortProfile_mono (mul_nonneg hD.le hTp.le) le_rfl
      (Nat.cast_nonneg M) (le_mul_of_one_le_left (Nat.cast_nonneg M) hD1)
      (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))).trans
      (universalShortProfile_scale hD1 hTp.le (Nat.cast_nonneg M)
        (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W)))
  exact h.trans ((mul_le_mul_of_nonneg_left hScale (by positivity)).trans_eq (by ring))

theorem reflection_complete_pair_energy_universal {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ,0<C ∧ ∀ T t₀ : ℝ,2≤T → ∀ M : ℕ,0<M → (M:ℝ)≤4*Real.sqrt T →
      ∀ W : Finset ℝ,(∀ t∈W,t∈Set.Icc t₀ (t₀+T)) →
        MathCollab.Density.completePairEnergy M W ≤
          C*T^η*universalShortProfile T M W.card (discreteAdditiveEnergy W) := by
  obtain ⟨C,hC,hBound⟩ := ratio_second_universal_uniform_translate η 64 hη (by norm_num)
  refine ⟨8*C,by positivity,?_⟩
  intro T t₀ hT M hM hMT W hW
  have hTp : 0<T := by linarith
  let Q := 2*M-1
  have hQ : 0<Q := by dsimp only [Q]; omega
  have hQM : (Q:ℝ)≤2*(M:ℝ) := by exact_mod_cast Nat.sub_le (2*M) 1
  have hQ2 : (Q:ℝ)^2≤64*T := by
    have hQnon : (0:ℝ)≤Q := Nat.cast_nonneg _
    have hs := Real.sq_sqrt hTp.le
    nlinarith [Real.sqrt_nonneg T]
  have hScale : universalShortProfile T Q W.card (discreteAdditiveEnergy W) ≤
      8*universalShortProfile T M W.card (discreteAdditiveEnergy W) := by
    have hh := universalShortProfile_mono hTp.le (by linarith : T≤2*T)
      (Nat.cast_nonneg Q) hQM (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
    have hs := universalShortProfile_scale (by norm_num : (1:ℝ)≤2) hTp.le
      (Nat.cast_nonneg M) (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
    norm_num only [pow_succ,pow_zero,mul_one] at hs
    exact hh.trans hs
  exact (completePairEnergy_le_doubled_ratio hM W).trans
    ((hBound T t₀ hT Q hQ hQ2 W hW).trans
      ((mul_le_mul_of_nonneg_left hScale (by positivity)).trans_eq (by ring)))

end Montgomery.RationalMoment
