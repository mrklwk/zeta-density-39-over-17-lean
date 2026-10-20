module
public import DensityWindowBudgets

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

/-- All endpoints and length-window budgets for the first two-term branch. -/
theorem two_term_window_first (s : ℝ) (hl : (12/17:ℝ) ≤ s) (hr : s ≤ (5/7:ℝ)) :
    TwoTermWindow s (2/(8*s-3)) (6*(1-s)/(8*s-3)) ((14*s-9)/((8*s-3)*(2*s-1))) := by
  have hD : 0 < 8*s-3 := by linarith
  have hE : 0 < 2*s-1 := by linarith
  have hDn : -3+s*8 ≠ 0 := by linarith
  have hEn : -1+s*2 ≠ 0 := by linarith
  have hPn : ((3:ℝ) + (-14:ℝ)*s + (16:ℝ)*s^2) ≠ 0 := by nlinarith only [mul_pos hD hE]
  ring_nf at hDn hEn hPn
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    p_identity := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
    mean_identity := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
    a_low := by
      have hid : (2/(8*s-3))-(7/10:ℝ) = ((41/10:ℝ) + (-28/5:ℝ)*s)/((8*s-3)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (41/10:ℝ) + (-28/5:ℝ)*s := by
        have h₀ : 0 ≤ (4165/2:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (17493/5:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (14161/10:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (2/(8*s-3))-(7/10:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    a_high := by
      have hid : (4/5:ℝ)-(2/(8*s-3)) = ((-22/5:ℝ) + (32/5:ℝ)*s)/((8*s-3)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-22/5:ℝ) + (32/5:ℝ)*s := by
        have h₀ : 0 ≤ (1666:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (20468/5:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (12138/5:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (4/5:ℝ)-(2/(8*s-3)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    p_low := by
      have hid : (6*(1-s)/(8*s-3))-(3/5:ℝ) = ((39/5:ℝ) + (-54/5:ℝ)*s)/((8*s-3)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (39/5:ℝ) + (-54/5:ℝ)*s := by
        have h₀ : 0 ≤ (2499:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (18564/5:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (6069/5:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (6*(1-s)/(8*s-3))-(3/5:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_low := by
      have hid : ((14*s-9)/((8*s-3)*(2*s-1)))-(2/(8*s-3)) = ((-7:ℝ) + (10:ℝ)*s)/((8*s-3)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-7:ℝ) + (10:ℝ)*s := by
        have h₀ : 0 ≤ (833:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (2856:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2023:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ ((14*s-9)/((8*s-3)*(2*s-1)))-(2/(8*s-3)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_high := by
      have hid : 1-((14*s-9)/((8*s-3)*(2*s-1))) = ((12:ℝ) + (-28:ℝ)*s + (16:ℝ)*s^2)/((8*s-3)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (12:ℝ) + (-28:ℝ)*s + (16:ℝ)*s^2 := by
        have h₀ : 0 ≤ (2940:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (5236:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2312:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 1-((14*s-9)/((8*s-3)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_range := by
      have hid : (6*(1-s)/(8*s-3))-2*(1-(2/(8*s-3))) = ((16:ℝ) + (-22:ℝ)*s)/((8*s-3)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (16:ℝ) + (-22:ℝ)*s := by
        have h₀ : 0 ≤ (6664:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (10710:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (4046:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (6*(1-s)/(8*s-3))-2*(1-(2/(8*s-3))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_lower := by
      have hid : (6*(1-s)/(8*s-3))+((14*s-9)/((8*s-3)*(2*s-1)))*(6*s-5) = ((39:ℝ) + (-106:ℝ)*s + (72:ℝ)*s^2)/((8*s-3)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (39:ℝ) + (-106:ℝ)*s + (72:ℝ)*s^2 := by
        have h₀ : 0 ≤ (735:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (952:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (289:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (6*(1-s)/(8*s-3))+((14*s-9)/((8*s-3)*(2*s-1)))*(6*s-5) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    cubic_lower := by
      have hid : (6*(1-s)/(8*s-3))+(2/(8*s-3))*(6*s-4)-(4/5:ℝ) = ((2/5:ℝ) + (-2/5:ℝ)*s)/((8*s-3)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (2/5:ℝ) + (-2/5:ℝ)*s := by
        have h₀ : 0 ≤ (1666:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (16422/5:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (8092/5:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (6*(1-s)/(8*s-3))+(2/(8*s-3))*(6*s-4)-(4/5:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_upper := by
      have hid : 1-((6*(1-s)/(8*s-3))+((14*s-9)/((8*s-3)*(2*s-1)))*(6*s-4)) = ((-27:ℝ) + (78:ℝ)*s + (-56:ℝ)*s^2)/((8*s-3)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-27:ℝ) + (78:ℝ)*s + (-56:ℝ)*s^2 := by
        have h₀ : 0 ≤ (2205:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (4284:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2023:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 1-((6*(1-s)/(8*s-3))+((14*s-9)/((8*s-3)*(2*s-1)))*(6*s-4)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    cubic_balance := by
      have hid : 5*(6*(1-s)/(8*s-3))/2+(2/(8*s-3))*(12*s-8)-2 = ((5:ℝ) + (-7:ℝ)*s)/((8*s-3)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (5:ℝ) + (-7:ℝ)*s := by
        have h₀ : 0 ≤ (833:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (833:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (0:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 5*(6*(1-s)/(8*s-3))/2+(2/(8*s-3))*(12*s-8)-2 := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_first := by
      have hid : 2*(6*(1-s)/(8*s-3))-(1+((14*s-9)/((8*s-3)*(2*s-1)))*(6-8*s)) = ((39:ℝ) + (-106:ℝ)*s + (72:ℝ)*s^2)/((8*s-3)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (39:ℝ) + (-106:ℝ)*s + (72:ℝ)*s^2 := by
        have h₀ : 0 ≤ (735:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (952:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (289:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 2*(6*(1-s)/(8*s-3))-(1+((14*s-9)/((8*s-3)*(2*s-1)))*(6-8*s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_resonant := by
      have hid : (6*(1-s)/(8*s-3))-(1+(2/(8*s-3))*(9/2-7*s)) = ((0:ℝ))/((8*s-3)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (0:ℝ) := by
        norm_num
      have hh : 0 ≤ (6*(1-s)/(8*s-3))-(1+(2/(8*s-3))*(9/2-7*s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    typeII := by
      have hid : (6*(1-s)/(8*s-3))-(2-2*s+1/25) = ((303/25:ℝ) + (-708/25:ℝ)*s + (16:ℝ)*s^2)/((8*s-3)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (303/25:ℝ) + (-708/25:ℝ)*s + (16:ℝ)*s^2 := by
        have h₀ : 0 ≤ (7203/5:ℝ)*((5/7:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (54978/25:ℝ)*((s-(12/17:ℝ))*((5/7:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (19363/25:ℝ)*(s-(12/17:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (6*(1-s)/(8*s-3))-(2-2*s+1/25) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
  }

/-- All endpoints and length-window budgets for the second two-term branch. -/
theorem two_term_window_second (s : ℝ) (hl : (5/7:ℝ) ≤ s) (hr : s ≤ (21/29:ℝ)) :
    TwoTermWindow s (4/(9*s-1)) (12*(1-s)/(9*s-1)) ((21*s-13)/((9*s-1)*(2*s-1))) := by
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
        have h₀ : 0 ≤ (41209/20:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (69629/20:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1421:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (4/(9*s-1))-(7/10:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    a_high := by
      have hid : (4/5:ℝ)-(4/(9*s-1)) = ((-24/5:ℝ) + (36/5:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-24/5:ℝ) + (36/5:ℝ)*s := by
        have h₀ : 0 ≤ (17661/5:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (38976/5:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (4263:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (4/5:ℝ)-(4/(9*s-1)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    p_low := by
      have hid : (12*(1-s)/(9*s-1))-(3/5:ℝ) = ((63/5:ℝ) + (-87/5:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (63/5:ℝ) + (-87/5:ℝ)*s := by
        have h₀ : 0 ≤ (17661/10:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (17661/10:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (0:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))-(3/5:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_low := by
      have hid : ((21*s-13)/((9*s-1)*(2*s-1)))-(4/(9*s-1)) = ((-9:ℝ) + (13:ℝ)*s)/((9*s-1)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-9:ℝ) + (13:ℝ)*s := by
        have h₀ : 0 ≤ (5887/2:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (14413/2:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (4263:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ ((21*s-13)/((9*s-1)*(2*s-1)))-(4/(9*s-1)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_high := by
      have hid : 1-((21*s-13)/((9*s-1)*(2*s-1))) = ((14:ℝ) + (-32:ℝ)*s + (18:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (14:ℝ) + (-32:ℝ)*s + (18:ℝ)*s^2 := by
        have h₀ : 0 ≤ (3364:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (6090:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2744:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 1-((21*s-13)/((9*s-1)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_range := by
      have hid : (12*(1-s)/(9*s-1))-2*(1-(4/(9*s-1))) = ((22:ℝ) + (-30:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (22:ℝ) + (-30:ℝ)*s := by
        have h₀ : 0 ≤ (5887:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (8729:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2842:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))-2*(1-(4/(9*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_lower := by
      have hid : (12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-5) = ((53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2 := by
        have h₀ : 0 ≤ (841/2:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (1421/2:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (392:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-5) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    cubic_lower := by
      have hid : (12*(1-s)/(9*s-1))+(4/(9*s-1))*(6*s-4)-(4/5:ℝ) = ((-16/5:ℝ) + (24/5:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-16/5:ℝ) + (24/5:ℝ)*s := by
        have h₀ : 0 ≤ (11774/5:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (25984/5:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2842:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))+(4/(9*s-1))*(6*s-4)-(4/5:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_upper := by
      have hid : 1-((12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-4)) = ((-39:ℝ) + (115:ℝ)*s + (-84:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-39:ℝ) + (115:ℝ)*s + (-84:ℝ)*s^2 := by
        have h₀ : 0 ≤ (5887/2:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (10759/2:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2352:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
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
        have h₀ : 0 ≤ (841/2:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (1421/2:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (392:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 2*(12*(1-s)/(9*s-1))-(1+((21*s-13)/((9*s-1)*(2*s-1)))*(6-8*s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_resonant := by
      have hid : (12*(1-s)/(9*s-1))-(1+(4/(9*s-1))*(9/2-7*s)) = ((-5:ℝ) + (7:ℝ)*s)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-5:ℝ) + (7:ℝ)*s := by
        have h₀ : 0 ≤ (0:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (1421/2:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1421/2:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))-(1+(4/(9*s-1))*(9/2-7*s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    typeII := by
      have hid : (12*(1-s)/(9*s-1))-(2-2*s+1/25) = ((351/25:ℝ) + (-809/25:ℝ)*s + (18:ℝ)*s^2)/((9*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (351/25:ℝ) + (-809/25:ℝ)*s + (18:ℝ)*s^2 := by
        have h₀ : 0 ≤ (56347/50:ℝ)*((21/29:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (78967/50:ℝ)*((s-(5/7:ℝ))*((21/29:ℝ)-s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2352/5:ℝ)*(s-(5/7:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (12*(1-s)/(9*s-1))-(2-2*s+1/25) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
  }

end Montgomery.RationalMoment
