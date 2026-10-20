module
public import GenericPeakWidth
public import TaoTrudgianYang2025.AtkinsonPairNativePacket

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Finset
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
namespace Montgomery.CriticalPeak

/-- Restricted actual critical-line peak count with arbitrary fixed natural log cap. -/
theorem restricted_peak_tail_of_count_log_cap {a g b η ε : ℝ} (m : ℕ)
    (hm : 4 ≤ m) (hb : 2 ≤ b) (hlogpow : 2*g+b ≤ (m : ℝ))
    (hCount : LocalMeanCount a g b) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ, 0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ, oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^a/V^(2*g+2*b)) := by
  let κ : ℝ := min η (1/1000)
  have hκ : 0 < κ := lt_min hη (by norm_num)
  have hκη : κ ≤ η := min_le_left _ _
  have hκcap : κ ≤ 1/48 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨K,D,B,hK,hD,hB,hcount⟩ :=
    exists_pointValue_card_le_source_range hb hCount
      (δ := (1/48:ℝ)) (κ := κ) (ν := ε/2)
      (by norm_num) (by norm_num) hκ (by linarith)
  have hlower := eventually_pointValue_source_lower_range hK hκ
  have hupper := TaoTrudgianYang2025.eventually_pointValue_sixth_power_source_range hK hκ hκcap
  have hGrowth := zetaMomentCriticalNorm_eventually_lt_slab_power hκ
  have hbudget := TaoTrudgianYang2025.eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := D) (a := ε/2) (b := ε) hD.le m (by linarith)
  have hlogs := eventually_pointValue_log_scales (P := (0:ℝ)) hK (by norm_num : (0:ℝ)<1)
  filter_upwards [eventually_ge_atTop B,hlower,hupper,hGrowth,hbudget,hlogs] with
    H hH hl hu hg hbud hlog
  intro V hV hVlower W hsep hrange hlarge
  have hH0 : 0 < H := by linarith [hB.trans hH]
  have hH1 : 1 ≤ H := by linarith [hB.trans hH]
  rcases W.eq_empty_or_nonempty with rfl | ⟨t,ht⟩
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  have hVgrowth : V ≤ H^(1/6+κ) :=
    (hlarge t ht).trans (hg t (by
      rw [abs_of_nonneg (by linarith [(hrange t ht).1] : 0 ≤ t)]
      exact (hrange t ht).2)).le
  have hVl : H^(1/8+κ) ≤ V :=
    (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans hVlower
  have hVsq := pow_le_pow_left₀ (by positivity : 0 ≤ H^(1/8+κ)) hVl 2
  have hVupper := pow_le_pow_left₀ hV.le hVgrowth 2
  have hc := hcount H V W hH hV (hl.trans hVsq) (hVupper.trans hu.2)
    hsep hrange hlarge
  have hL1 : 1 ≤ Real.log (3*H) := hlog.2.1
  have hL0 : 0 ≤ Real.log (3*H) := by linarith
  have h4 : (Real.log (3*H))^4 ≤ (Real.log (3*H))^m :=
    pow_le_pow_right₀ hL1 hm
  have hr : (Real.log (3*H))^(2*g+b) ≤ (Real.log (3*H))^m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL1 hlogpow
  calc
    (W.card:ℝ) ≤ D*H^(ε/2)*
        (H*(Real.log (3*H))^4/V^6+H^a*(Real.log (3*H))^(2*g+b)/V^(2*g+2*b)) := hc
    _ ≤ D*H^(ε/2)*
        (H*(Real.log (3*H))^m/V^6+H^a*(Real.log (3*H))^m/V^(2*g+2*b)) := by
      gcongr
    _ = (D*(Real.log (3*H))^m*H^(ε/2))*(H/V^6+H^a/V^(2*g+2*b)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbud (by positivity)
/-- Every fixed logarithmic exponent can be absorbed into the height loss. -/
theorem restricted_peak_tail_of_count_general {a g b η ε : ℝ}
    (hb : 2 ≤ b) (hCount : LocalMeanCount a g b) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ, 0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ, oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^a/V^(2*g+2*b)) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (max (4:ℝ) (2*g+b))
  have hm4 : (4:ℝ) ≤ (m:ℝ) := (le_max_left _ _).trans hm
  exact restricted_peak_tail_of_count_log_cap m (by exact_mod_cast hm4) hb
    ((le_max_right _ _).trans hm) hCount hη hε
end Montgomery.CriticalPeak

namespace TaoTrudgianYang2025
open Montgomery.CriticalPeak
/-- The actual analytic exponent pair and both native zeta sources supply the restricted tail. -/
theorem ExponentPair.restricted_critical_peak_tail_general {k l η ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ, 0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ, oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^(1+l/k)/V^(4+(2+4*l)/k)) := by
  have hb : (2:ℝ) ≤ 2+2/k := le_add_of_nonneg_right (by positivity)
  have hf : 2*((2*l-1)/k)+2*(2+2/k) = 4+(2+4*l)/k := by ring
  have hh := restricted_peak_tail_of_count_general hb
    (a := 1+l/k) (g := (2*l-1)/k) (b := 2+2/k)
    (localMeanCount_of_pair_packet hk hpair.localMeanPacket_native) hη hε
  simpa only [hf] using hh
end TaoTrudgianYang2025
