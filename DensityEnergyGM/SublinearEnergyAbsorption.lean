module
public import DensityEnergyGM.SecondMomentPowerAlgebra

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

theorem sublinear_energy_power_solve {E A V p : ℝ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hV : 0 < V) (hp : p < 1)
    (h : E * V ^ 2 ≤ A * E ^ p) :
    E ≤ (A / V ^ 2) ^ (1 / (1 - p)) := by
  by_cases hEpos : 0 < E
  · have hEp : 0 < E ^ p := Real.rpow_pos_of_pos hEpos p
    have hId : E ^ p * E ^ (1 - p) = E := by
      rw [← Real.rpow_add hEpos, show p + (1 - p) = 1 by ring, Real.rpow_one]
    have hCancel : E ^ (1 - p) * V ^ 2 ≤ A := by
      apply le_of_mul_le_mul_left (a := E ^ p) ?_ hEp
      calc
        E ^ p * (E ^ (1 - p) * V ^ 2) = E * V ^ 2 := by rw [← mul_assoc, hId]
        _ ≤ A * E ^ p := h
        _ = E ^ p * A := mul_comm _ _
    have hBase : E ^ (1 - p) ≤ A / V ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hV)).mpr hCancel
    have hRaise := Real.rpow_le_rpow (Real.rpow_nonneg hE (1 - p))
      hBase (show 0 ≤ 1 / (1 - p) by positivity)
    have hPower : (E ^ (1 - p)) ^ (1 / (1 - p)) = E := by
      rw [← Real.rpow_mul hE]
      have hExp : (1 - p) * (1 / (1 - p)) = 1 := by
        have hpne : 1 - p ≠ 0 := by linarith
        field_simp [hpne]
      rw [hExp, Real.rpow_one]
    rw [hPower] at hRaise
    exact hRaise
  · have heq : E = 0 := by linarith
    rw [heq]
    exact Real.rpow_nonneg (div_nonneg hA (sq_nonneg V)) _

theorem five_sublinear_energy_absorption {E V A B C D F p q r s t : ℝ}
    (hE : 0 ≤ E) (hV : 0 < V)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hp : p < 1) (hq : q < 1) (hr : r < 1) (hs : s < 1) (ht : t < 1)
    (h : E * V ^ 2 ≤ A * E ^ p + B * E ^ q + C * E ^ r + D * E ^ s + F * E ^ t) :
    E ≤ (5 * A / V ^ 2) ^ (1 / (1 - p)) +
      (5 * B / V ^ 2) ^ (1 / (1 - q)) +
      (5 * C / V ^ 2) ^ (1 / (1 - r)) +
      (5 * D / V ^ 2) ^ (1 / (1 - s)) +
      (5 * F / V ^ 2) ^ (1 / (1 - t)) := by
  have hFirst : E * V ^ 2 ≤ 5 * A * E ^ p ∨
      E * V ^ 2 ≤ 5 * B * E ^ q ∨ E * V ^ 2 ≤ 5 * C * E ^ r ∨
      E * V ^ 2 ≤ 5 * D * E ^ s ∨ E * V ^ 2 ≤ 5 * F * E ^ t := by
    by_contra! hnot
    rcases hnot with ⟨ha, hb, hc, hd, hf⟩
    linarith
  have h1 : 0 ≤ (5 * A / V ^ 2) ^ (1 / (1 - p)) := by positivity
  have h2 : 0 ≤ (5 * B / V ^ 2) ^ (1 / (1 - q)) := by positivity
  have h3 : 0 ≤ (5 * C / V ^ 2) ^ (1 / (1 - r)) := by positivity
  have h4 : 0 ≤ (5 * D / V ^ 2) ^ (1 / (1 - s)) := by positivity
  have h5 : 0 ≤ (5 * F / V ^ 2) ^ (1 / (1 - t)) := by positivity
  rcases hFirst with h | h | h | h | h
  · have hh := sublinear_energy_power_solve hE (by positivity : 0 ≤ 5 * A) hV hp h
    linarith
  · have hh := sublinear_energy_power_solve hE (by positivity : 0 ≤ 5 * B) hV hq h
    linarith
  · have hh := sublinear_energy_power_solve hE (by positivity : 0 ≤ 5 * C) hV hr h
    linarith
  · have hh := sublinear_energy_power_solve hE (by positivity : 0 ≤ 5 * D) hV hs h
    linarith
  · have hh := sublinear_energy_power_solve hE (by positivity : 0 ≤ 5 * F) hV ht h
    linarith

end Montgomery.RationalMoment
