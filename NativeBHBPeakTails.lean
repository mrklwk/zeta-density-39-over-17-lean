module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import TaoTrudgianYang2025.ExponentPairBProcess
public import GenericRestrictedPeakTail

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Finset
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
namespace TaoTrudgianYang2025

theorem exponentPair_BHB10 : ExponentPair (64/135) (122/243) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (10:ℕ))).bProcess using 1 <;> norm_num

theorem exponentPair_BHB9 : ExponentPair (371/792) (177/352) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (9:ℕ))).bProcess using 1 <;> norm_num

theorem exponentPair_BHB8 : ExponentPair (129/280) (247/490) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (8:ℕ))).bProcess using 1 <;> norm_num

theorem exponentPair_BHB7 : ExponentPair (85/189) (41/81) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (7:ℕ))).bProcess using 1 <;> norm_num

theorem exponentPair_BHB6 : ExponentPair (13/30) (51/100) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (6:ℕ))).bProcess using 1 <;> norm_num

/-- Native BHB10 tail for the actual critical zeta values, with no analytic premise. -/
theorem critical_peak_tail_BHB10 {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ,oneSeparated W →
        (∀ t ∈ W,H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W,V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^((593:ℝ)/288)/V^((3587:ℝ)/288)) := by
  simpa only [show (1:ℝ)+(122/243)/(64/135)=593/288 by norm_num,
    show (4:ℝ)+(2+4*(122/243))/(64/135)=3587/288 by norm_num] using
    exponentPair_BHB10.restricted_critical_peak_tail (by norm_num) (by norm_num) hη hε

theorem critical_peak_tail_BHB9 {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ,oneSeparated W →
        (∀ t ∈ W,H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W,V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^((3077:ℝ)/1484)/V^((4661:ℝ)/371)) := by
  simpa only [show (1:ℝ)+(177/352)/(371/792)=3077/1484 by norm_num,
    show (4:ℝ)+(2+4*(177/352))/(371/792)=4661/371 by norm_num] using
    exponentPair_BHB9.restricted_critical_peak_tail (by norm_num) (by norm_num) hη hε

theorem critical_peak_tail_BHB8 {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ,oneSeparated W →
        (∀ t ∈ W,H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W,V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^((1891:ℝ)/903)/V^((3828:ℝ)/301)) := by
  simpa only [show (1:ℝ)+(247/490)/(129/280)=1891/903 by norm_num,
    show (4:ℝ)+(2+4*(247/490))/(129/280)=3828/301 by norm_num] using
    exponentPair_BHB8.restricted_critical_peak_tail (by norm_num) (by norm_num) hη hε

theorem critical_peak_tail_BHB7 {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ,oneSeparated W →
        (∀ t ∈ W,H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W,V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^((542:ℝ)/255)/V^((3302:ℝ)/255)) := by
  simpa only [show (1:ℝ)+(41/81)/(85/189)=542/255 by norm_num,
    show (4:ℝ)+(2+4*(41/81))/(85/189)=3302/255 by norm_num] using
    exponentPair_BHB7.restricted_critical_peak_tail (by norm_num) (by norm_num) hη hε
theorem critical_peak_tail_BHB6 {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ,0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ,oneSeparated W →
        (∀ t ∈ W,H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W,V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^((283:ℝ)/130)/V^((866:ℝ)/65)) := by
  simpa only [show (1:ℝ)+(51/100)/(13/30)=283/130 by norm_num,
    show (4:ℝ)+(2+4*(51/100))/(13/30)=866/65 by norm_num] using
    exponentPair_BHB6.restricted_critical_peak_tail (by norm_num) (by norm_num) hη hε
end TaoTrudgianYang2025
