module
/- Generalized from the attributed verified physical-width argument. -/
public import PeakWidthPowers
public import MathCollab.Density.Stronger.Peaks.WidthRanges

@[expose] public section
open Filter Finset
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
set_option autoImplicit false
noncomputable section
namespace Montgomery.CriticalPeak
theorem exists_pointValue_card_le_source_range
    {a g b : ℝ} (hb : 2 ≤ b) (hCount : LocalMeanCount a g b)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hδUpper : δ ≤ 1/4)
    (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ K D H₀ : ℝ, 0 < K ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < V →
        K*(Real.log (3*H))^2*(2*H)^(1/4+κ) ≤ V^2 →
        V^2 ≤ K*(Real.log (3*H))^2*H^(1/2-δ) →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H*(Real.log (3*H))^4/V^6 + H^a*(Real.log (3*H))^(2*g+b)/V^(2*g+2*b)) := by
  obtain ⟨P,C,D,B,hP,hC,hD,hB,hcount⟩ :=
    (exists_pointValue_card_le_with_width hb hCount) hδ hκ hν
  let K : ℝ := 16*P*C+1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKsize : 16*P*C ≤ K := by dsimp only [K]; linarith
  have hq : 0 < (1/4:ℝ)+κ := by linarith
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp
    (eventually_pointValue_log_scales (P := P) hK hq)
  let D₁ : ℝ := D*(K*(16*P)^2+K^g*(16*P)^b)
  have hD₁ : 0 < D₁ := by dsimp only [D₁]; positivity
  refine ⟨K,D₁,max B B₁,hK,hD₁,le_max_of_le_left hB,?_⟩
  intro H V W hH hV hLower hUpper hsep hrange hlarge
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  obtain ⟨hH20,hL1,hPL,hlogFit⟩ := hB₁ H ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  let L : ℝ := Real.log (3*H)
  let G : ℝ := V^2/(K*L^2)
  have hL : 0 < L := by dsimp only [L]; linarith
  have hDen : 0 < K*L^2 := by positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  have hGlo : (2*H)^(1/4+κ) ≤ G := by
    dsimp only [G]
    exact (le_div_iff₀ hDen).mpr (by simpa only [L,mul_comm] using hLower)
  have hGhi : G ≤ H^(1/2-δ) := by
    dsimp only [G]
    exact (div_le_iff₀ hDen).mpr (by simpa only [L,mul_comm] using hUpper)
  have hGH : G ≤ H := by
    calc
      G ≤ H^(1/2-δ) := hGhi
      _ ≤ H^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
      _ = H := Real.rpow_one H
  have hfit : 2*(Real.log (3*H))^2 ≤ G :=
    hlogFit.trans ((Real.rpow_le_rpow hH0.le (by linarith) hq.le).trans hGlo)
  have hwidth : ∀ t : ℝ, H ≤ t → t ≤ 2*H →
      t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G := by
    intro t htlo hthi
    have ht0 : 0 ≤ t := hH0.le.trans htlo
    refine ⟨?_,?_,?_⟩
    · calc
        t^δ ≤ (2*H)^δ := Real.rpow_le_rpow ht0 hthi hδ.le
        _ ≤ (2*H)^(1/4+κ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ ≤ G := hGlo
    · exact hGhi.trans (Real.rpow_le_rpow hH0.le htlo (by linarith))
    · exact (Real.rpow_le_rpow ht0 hthi hq.le).trans hGlo
  have hOnePow : 1 ≤ (2*H)^(1/4+κ) :=
    Real.one_le_rpow (by linarith) hq.le
  have hLowerSimple : K*L^2 ≤ V^2 := by
    have hm := mul_le_mul_of_nonneg_left hOnePow hDen.le
    have hLower' : K*L^2*(2*H)^(1/4+κ) ≤ V^2 := hLower
    nlinarith
  have hVsize : 2*P*Real.log (3*H) ≤ V^2 := by
    have hm := mul_le_mul_of_nonneg_right hPL hL.le
    change 2*P*L ≤ V^2
    change 2*P*L ≤ K*L*L at hm
    nlinarith
  have herr : C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) :=
    pointValueWidth_error_absorption hP hK hL hKsize
  have hc := hcount H G V W hHB hG hGH hV hfit hwidth hVsize herr
    hsep hrange hlarge
  change (W.card:ℝ) ≤ D*H^ν*(H/(G*(V^2/(16*P*L))^2)+
    H^a/(G^g*(V^2/(16*P*L))^b)) at hc
  have he1 := width_first_term (H := H) hK hP hL hV
  have he2 := width_second_term (a := a) (g := g) (b := b) (H := H) hK hP hL hV
  change H/(G*(V^2/(16*P*L))^2) = _ at he1
  change H^a/(G^g*(V^2/(16*P*L))^b) = _ at he2
  rw [he1,he2] at hc
  have hx : 0 ≤ H*L^4/V^6 := by positivity
  have hy : 0 ≤ H^a*L^(2*g+b)/V^(2*g+2*b) := by positivity
  have hkx : 0 ≤ K*(16*P)^2 := by positivity
  have hky : 0 ≤ K^g*(16*P)^b := by positivity
  calc
    (W.card:ℝ) ≤ D*H^ν*
        (K*(16*P)^2*(H*L^4/V^6)+K^g*(16*P)^b*(H^a*L^(2*g+b)/V^(2*g+2*b)))  := by convert hc using 1; ring
    _ ≤ D*H^ν*((K*(16*P)^2+K^g*(16*P)^b)*
        (H*L^4/V^6+H^a*L^(2*g+b)/V^(2*g+2*b))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hkx hy,mul_nonneg hky hx]
    _ = D₁*H^ν*(H*(Real.log (3*H))^4/V^6+H^a*(Real.log (3*H))^(2*g+b)/V^(2*g+2*b)) := by
      dsimp only [D₁,L]
      ring




end Montgomery.CriticalPeak
