/- A weak actual mollified fourth moment from the ordinary fourth moment.
The fixed power loss 1/25 is intentional; this does not assert
ShortMobiusFourthMoment. -/
import GuthMaynard.Improvement.ShortDetectorLocalMass
import MathCollab.Density.Stronger.Fourth.FourthMoment
set_option autoImplicit false
noncomputable section
open MeasureTheory Set MathCollab.Density MathCollab.Density.Stronger
open scoped Interval
namespace GuthMaynard.Improvement

theorem shortTwistedNorm_fourth_le {H : ℝ} (hH : 0 ≤ H) (t : ℝ) :
    (shortTwistedNorm H t)^4 ≤
      16*H^((1:ℝ)/25)*(zetaMomentCriticalNorm t)^4 := by
  have hm := (norm_zetaMollifier_le_cutoff (2*H^((1:ℝ)/100))
    (s := (1/2:ℂ)+(t:ℂ)*Complex.I) (by norm_num)).trans
    (Nat.floor_le (by positivity))
  have hp : shortTwistedNorm H t ≤ zetaMomentCriticalNorm t*(2*H^((1:ℝ)/100)) := by
    unfold shortTwistedNorm zetaMomentCriticalNorm
    rw [norm_mul]
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      mul_le_mul_of_nonneg_left hm (norm_nonneg (riemannZeta ((1/2:ℂ)+(t:ℂ)*Complex.I)))
  have hh := pow_le_pow_left₀ (show 0 ≤ shortTwistedNorm H t by unfold shortTwistedNorm; positivity) hp 4
  have he : (H^((1:ℝ)/100))^4 = H^((1:ℝ)/25) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hH]; norm_num
  simp only [mul_pow,he] at hh
  nlinarith [hh]

/-- Constants precede height; the norm and integration interval are literal. -/
theorem weak_short_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C H0 : ℝ, 0 < C ∧ 2 ≤ H0 ∧ ∀ H : ℝ, H0 ≤ H →
      (∫ t in Icc (H/2) (3*H), (shortTwistedNorm H t)^4) ≤
        C*H^(1+(1:ℝ)/25+ε) := by
  obtain ⟨B,Hb,hB,hb⟩ := Fourth.zeta_fourth_dyadic ε hε
  refine ⟨48*(B+1)*2^(1+ε),max 2 (2*Hb),by positivity,le_max_left _ _,?_⟩
  intro H hH
  have hH2 : 2 ≤ H := (le_max_left _ _).trans hH
  have hHb : 2*Hb ≤ H := (le_max_right _ _).trans hH
  have hpos : 0 < H := by linarith
  let f : ℝ → ℝ := fun t => (zetaMomentCriticalNorm t)^4
  have hc : Continuous f := continuous_zetaMomentCriticalNorm.pow 4
  have hf0 (t : ℝ) : 0 ≤ f t := by exact pow_nonneg (norm_nonneg _) _
  have hbound (x : ℝ) (hx : Hb ≤ x) (hx0 : 0 < x) (hxH : x ≤ 2*H) :
      (∫ t in x..2*x, f t) ≤ (B+1)*(2*H)^(1+ε) := by
    calc
      _ ≤ B*x^(1+ε) := hb x hx hx0
      _ ≤ (B+1)*(2*H)^(1+ε) := mul_le_mul
        (by linarith) (Real.rpow_le_rpow hx0.le hxH (by linarith))
        (by positivity) (by positivity)
  have h1 := hbound (H/2) (by linarith) (by positivity) (by linarith)
  have h2 := hbound H (by linarith) hpos (by linarith)
  have h3 := hbound (2*H) (by linarith) (by positivity) le_rfl
  have hs : (∫ t in H/2..4*H, f t) ≤ 3*(B+1)*(2*H)^(1+ε) := by
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) (a := H/2) (b := H)) (hc.intervalIntegrable (μ := volume) (a := H) (b := 2*H))
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) (a := H/2) (b := 2*H)) (hc.intervalIntegrable (μ := volume) (a := 2*H) (b := 4*H))
    have hhalf : 2*(H/2)=H := by ring
    have hdouble : 2*(2*H)=4*H := by ring
    rw [hhalf] at h1
    rw [hdouble] at h3
    linarith
  have hi : (∫ t in Icc (H/2) (3*H),f t) ≤ 3*(B+1)*(2*H)^(1+ε) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : H/2 ≤ 3*H)]
    exact (intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall hf0) (hc.intervalIntegrable (μ := volume) (a := H/2) (b := 4*H))).trans hs
  calc
    _ ≤ ∫ t in Icc (H/2) (3*H),16*H^((1:ℝ)/25)*f t := by
      apply integral_mono ((shortTwistedNorm_continuous H).pow 4).integrableOn_Icc
        (hc.const_mul _).integrableOn_Icc
      exact fun t => shortTwistedNorm_fourth_le hpos.le t
    _ = (16*H^((1:ℝ)/25))*(∫ t in Icc (H/2) (3*H),f t) := integral_const_mul _ _
    _ ≤ (16*H^((1:ℝ)/25))*(3*(B+1)*(2*H)^(1+ε)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hpos.le]
      have he : H^((1:ℝ)/25)*H^(1+ε)=H^(1+1/25+ε) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      calc
        _ = (48*(B+1)*2^(1+ε))*(H^((1:ℝ)/25)*H^(1+ε)) := by ring
        _ = _ := by rw [he]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.shortTwistedNorm_fourth_le
#print axioms GuthMaynard.Improvement.weak_short_moment
