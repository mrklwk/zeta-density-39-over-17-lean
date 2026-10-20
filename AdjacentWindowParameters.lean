module
public import AdjacentWindow

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

/-- All endpoints and length-window budgets for the second two-term branch. -/
theorem adjacent_window_second (s : ℝ) (hl : (5/7:ℝ) ≤ s) (hr : s ≤ (113/153:ℝ)) :
    AdjacentWindow s (4/(9*s-1)) (12*(1-s)/(9*s-1)) ((21*s-13)/((9*s-1)*(2*s-1))) := by
  have hD : 0 < 9*s-1 := by linarith
  have hE : 0 < 2*s-1 := by linarith
  have hDn : -1+s*9 ≠ 0 := by linarith
  have hEn : -1+s*2 ≠ 0 := by linarith
  have hPn : ((1:ℝ) + (-11:ℝ)*s + (18:ℝ)*s^2) ≠ 0 := by nlinarith only [mul_pos hD hE]
  ring_nf at hDn hEn hPn
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    p_identity := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
    mean_identity := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
    a_low := by
      have hid : (4/(9*s-1))-(7/10:ℝ) = ((47/10:ℝ) + (-63/10:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (47/10:ℝ) + (-63/10:ℝ)*s := by
        have h₀ : 0 ≤ (1147041/3380:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (1416933/3380:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (67473/845:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (4/(9*s-1))-(7/10:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    a_high := by
      have hid : (4/5:ℝ)-(4/(9*s-1)) = ((-24/5:ℝ) + (36/5:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-24/5:ℝ) + (36/5:ℝ)*s := by
        have h₀ : 0 ≤ (491589/845:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (1233792/845:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (742203/845:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (4/5:ℝ)-(4/(9*s-1)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    p_low := by
      have hid : (12*(1-s)/(9*s-1))-(5/9:ℝ) = ((113/9:ℝ) + (-17:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (113/9:ℝ) + (-17:ℝ)*s := by
        have h₀ : 0 ≤ (18207/26:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (18207/26:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (0:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))-(5/9:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_low := by
      have hid : ((21*s-13)/((9*s-1)*(2*s-1)))-(4/(9*s-1)) = ((-9:ℝ) + (13:ℝ)*s)/((9*s-1)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-9:ℝ) + (13:ℝ)*s := by
        have h₀ : 0 ≤ (163863/338:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (508725/338:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (172431/169:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ ((21*s-13)/((9*s-1)*(2*s-1)))-(4/(9*s-1)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_high := by
      have hid : 1-((21*s-13)/((9*s-1)*(2*s-1))) = ((14:ℝ) + (-32:ℝ)*s + (18:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (14:ℝ) + (-32:ℝ)*s + (18:ℝ)*s^2 := by
        have h₀ : 0 ≤ (93636/169:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (143514/169:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (52920/169:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 1-((21*s-13)/((9*s-1)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_lower := by
      have hid : (12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-5) = ((53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2 := by
        have h₀ : 0 ≤ (23409/338:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (28917/338:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (19992/169:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-5) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    cubic_lower := by
      have hid : (12*(1-s)/(9*s-1))+(4/(9*s-1))*(6*s-4)-(4/5:ℝ) = ((-16/5:ℝ) + (24/5:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-16/5:ℝ) + (24/5:ℝ)*s := by
        have h₀ : 0 ≤ (327726/845:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (822528/845:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (494802/845:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))+(4/(9*s-1))*(6*s-4)-(4/5:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_upper := by
      have hid : 1-((12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-4)) = ((-39:ℝ) + (115:ℝ)*s + (-84:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-39:ℝ) + (115:ℝ)*s + (-84:ℝ)*s^2 := by
        have h₀ : 0 ≤ (163863/338:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (258111/338:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (32928/169:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 1-((12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-4)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    cubic_balance := by
      have hid : 5*(12*(1-s)/(9*s-1))/2+(4/(9*s-1))*(12*s-8)-2 = ((0:ℝ))/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (0:ℝ) := by
        norm_num
      have hh : 0 ≤ 5*(12*(1-s)/(9*s-1))/2+(4/(9*s-1))*(12*s-8)-2 := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_first := by
      have hid : 2*(12*(1-s)/(9*s-1))-(1+((21*s-13)/((9*s-1)*(2*s-1)))*(6-8*s)) = ((53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2 := by
        have h₀ : 0 ≤ (23409/338:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (28917/338:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (19992/169:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 2*(12*(1-s)/(9*s-1))-(1+((21*s-13)/((9*s-1)*(2*s-1)))*(6-8*s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_resonant := by
      have hid : (12*(1-s)/(9*s-1))-(1+(4/(9*s-1))*(9/2-7*s)) = ((-5:ℝ) + (7:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-5:ℝ) + (7:ℝ)*s := by
        have h₀ : 0 ≤ (0:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (7497/26:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (7497/26:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))-(1+(4/(9*s-1))*(9/2-7*s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_adjacent_third := by
      have hid : (5/2)*(12*(1-s)/(9*s-1))+(4/(9*s-1))*(14*s-8)-3 = ((1:ℝ) + (-1:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (1:ℝ) + (-1:ℝ)*s := by
        have h₀ : 0 ≤ (163863/338:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (313803/338:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (74970/169:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (5/2)*(12*(1-s)/(9*s-1))+(4/(9*s-1))*(14*s-8)-3 := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_adjacent_fourth := by
      have hid : (29/12)*(12*(1-s)/(9*s-1))+(4/(9*s-1))*(14*s-9)-9/4 = ((-19/4:ℝ) + (27/4:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring; have hi := mul_inv_cancel₀ hDn; nlinarith only [hi]
      have hpoly : 0 ≤ (-19/4:ℝ) + (27/4:ℝ)*s := by
        have h₀ : 0 ≤ (163863/1352:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (703647/1352:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (67473/169:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (29/12)*(12*(1-s)/(9*s-1))+(4/(9*s-1))*(14*s-9)-9/4 := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    typeII := by
      have hid : (12*(1-s)/(9*s-1))-(2-2*s+1/50) = ((701/50:ℝ) + (-1609/50:ℝ)*s + (18:ℝ)*s^2)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (701/50:ℝ) + (-1609/50:ℝ)*s + (18:ℝ)*s^2 := by
        have h₀ : 0 ≤ (6250203/16900:ℝ)*((113/153:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (7999299/16900:ℝ)*((s-(5/7:ℝ))*((113/153:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (513324/4225:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))-(2-2*s+1/50) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
  }

end Montgomery.RationalMoment
