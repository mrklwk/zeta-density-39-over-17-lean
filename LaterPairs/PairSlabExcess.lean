module
public import LaterPairs.RestrictedPeakTail
public import IntervalExcessTransfer
public import MathCollab.Density.Stronger.SeparatedVolume

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
namespace TaoTrudgianYang2025
open MathCollab.Density MathCollab.Density.Stronger
open Montgomery.RationalMoment.RightDetector

theorem ExponentPair.critical_slab_excess_general {k l η ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ v : ℝ, 0 < v → H^(1/8+η) ≤ v →
      (∫ t in Icc H (2*H),criticalExcess v t) ≤
        (2/5)*H^(1+ε)*v^(-5:ℝ)+
          (2/(3+(2+4*l)/k))*H^(1+l/k+ε)*v^(-3-(2+4*l)/k) := by
  have hq : 1 < 4+(2+4*l)/k := by
    have hl : 1/2 ≤ l := hpair.inTriangle.2.2.1
    have hp : 0 < (2+4*l)/k := div_pos (by linarith) hk
    linarith
  filter_upwards [hpair.restricted_critical_peak_tail_general hk hη hε,
    eventually_ge_atTop (1:ℝ)] with H hsource hH
  intro v hv hvrange
  have hH0 : 0 < H := by linarith
  have hfirst : H^ε*H=H^(1+ε) := by
    rw [Real.rpow_add hH0,Real.rpow_one]
    ring
  have hsecond : H^ε*H^(1+l/k)=H^(1+l/k+ε) := by
    rw [← Real.rpow_add hH0]
    congr 1
    ring
  have htail : ∀ u : ℝ,v ≤ u →
      volume.real {t : ℝ | t ∈ Icc H (2*H) ∧ u ≤ zetaMomentCriticalNorm t} ≤
        (2*H^(1+ε))*u^(-6:ℝ)+(2*H^(1+l/k+ε))*u^(-(4+(2+4*l)/k)) := by
    intro u hu
    have hu0 : 0 < u := hv.trans_le hu
    have hc : ∀ W : Finset ℝ,
        (∀ t ∈ W,t ∈ {x : ℝ | x ∈ Icc H (2*H) ∧ u ≤ zetaMomentCriticalNorm x}) →
        oneSeparated W → (W.card:ℝ) ≤ H^ε*(H/u^6+H^(1+l/k)/u^(4+(2+4*l)/k)) := by
      intro W hW hs
      exact hsource u hu0 (hvrange.trans hu) W hs
        (fun t ht => (hW t ht).1) (fun t ht => (hW t ht).2)
    have hm := volume_le_two_mul_of_separated_card_bound hc
    have hr := ENNReal.toReal_le_of_le_ofReal (by positivity) hm
    have he6 : u^(-6:ℝ)=1/u^6 := by
      rw [Real.rpow_neg hu0.le]
      norm_num [one_div]
    rw [he6,Real.rpow_neg hu0.le]
    convert hr using 1
    · rfl
    · rw [← hfirst,← hsecond]
      ring
  have hh := critical_excess_integral_le_two_tails_interval hv hq htail
  convert hh using 1
  congr 1 <;> ring_nf
end TaoTrudgianYang2025
