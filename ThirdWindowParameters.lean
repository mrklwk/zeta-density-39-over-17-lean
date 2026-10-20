module
public import ThirdWindow

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Montgomery.RationalMoment

/-- Every exponent and detecting length for the full third orange segment. -/
theorem third_window_parameters (s : ℝ) (hl : (113/153:ℝ) ≤ s) (hr : s ≤ (3/4:ℝ)) :
    ThirdWindow s (85/(153*s+7)) (255*(1-s)/(153*s+7)) ((408*s-248)/((153*s+7)*(2*s-1))) := by
  have hD : 0 < 153*s+7 := by linarith
  have hE : 0 < 2*s-1 := by linarith
  have hDn : 7+s*153 ≠ 0 := by linarith
  have hEn : -1+s*2 ≠ 0 := by linarith
  have hPn : ((-7:ℝ) + (-139:ℝ)*s + (306:ℝ)*s^2) ≠ 0 := by nlinarith only [mul_pos hD hE]
  ring_nf at hDn hEn hPn
  have hb0 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (1:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*x := by
    have he (y : ℝ) : (1:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*y = ((-1:ℝ))*y+((1:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (1:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*(85/(153*s+7)) = ((-78:ℝ) + (153:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-78:ℝ) + (153:ℝ)*s := by
        have h₀ : 0 ≤ (1872720/7:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (3839076/7:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (280908:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (1:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (1:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*((408*s-248)/((153*s+7)*(2*s-1))) = ((241:ℝ) + (-547:ℝ)*s + (306:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (241:ℝ) + (-547:ℝ)*s + (306:ℝ)*s^2 := by
        have h₀ : 0 ≤ (1468800/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (2530620/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1076814/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (1:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb1 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (1/6:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((0:ℝ))*x := by
    have he (y : ℝ) : (1/6:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((0:ℝ))*y = ((0:ℝ))*y+((1/6:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (1/6:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((0:ℝ))*(85/(153*s+7)) = ((7/6:ℝ) + (51/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (7/6:ℝ) + (51/2:ℝ)*s := by
        have h₀ : 0 ≤ (7490880/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (15091002/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (7600122/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (1/6:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((0:ℝ))*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (1/6:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((0:ℝ))*((408*s-248)/((153*s+7)*(2*s-1))) = ((-7/6:ℝ) + (-139/6:ℝ)*s + (51:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-7/6:ℝ) + (-139/6:ℝ)*s + (51:ℝ)*s^2 := by
        have h₀ : 0 ≤ (3574080/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (7371642/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (3800061/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (1/6:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((0:ℝ))*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb2 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-1:ℝ)+(3/2:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*x := by
    have he (y : ℝ) : (-1:ℝ)+(3/2:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*y = ((-4:ℝ) + (6:ℝ)*s)*y+((-1:ℝ)+(3/2:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-1:ℝ)+(3/2:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) = ((71/2:ℝ) + (-51/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (71/2:ℝ) + (-51/2:ℝ)*s := by
        have h₀ : 0 ≤ (6242400/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (12375558/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (6133158/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-1:ℝ)+(3/2:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-1:ℝ)+(3/2:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((1233/2:ℝ) + (-3667/2:ℝ)*s + (1377:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (1233/2:ℝ) + (-3667/2:ℝ)*s + (1377:ℝ)*s^2 := by
        have h₀ : 0 ≤ (5042880/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (10944702/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (5969295/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-1:ℝ)+(3/2:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb3 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-2:ℝ) + (2:ℝ)*s)*x := by
    have he (y : ℝ) : (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-2:ℝ) + (2:ℝ)*s)*y = ((-2:ℝ) + (2:ℝ)*s)*y+((0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-2:ℝ) + (2:ℝ)*s)*(85/(153*s+7)) = ((85:ℝ) + (-85:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (85:ℝ) + (-85:ℝ)*s := by
        have h₀ : 0 ≤ (8323200/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (16282260/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (7959060/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-2:ℝ) + (2:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-2:ℝ) + (2:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((241:ℝ) + (-547:ℝ)*s + (306:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (241:ℝ) + (-547:ℝ)*s + (306:ℝ)*s^2 := by
        have h₀ : 0 ≤ (1468800/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (2530620/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1076814/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-2:ℝ) + (2:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb4 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ) + (2:ℝ)*s)*x := by
    have he (y : ℝ) : (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ) + (2:ℝ)*s)*y = ((-1:ℝ) + (2:ℝ)*s)*y+((-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ) + (2:ℝ)*s)*(85/(153*s+7)) = ((985/6:ℝ) + (-425/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (985/6:ℝ) + (-425/2:ℝ)*s := by
        have h₀ : 0 ≤ (2705040/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (4499730/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1794690/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ) + (2:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ) + (2:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((-7/6:ℝ) + (-139/6:ℝ)*s + (51:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-7/6:ℝ) + (-139/6:ℝ)*s + (51:ℝ)*s^2 := by
        have h₀ : 0 ≤ (3574080/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (7371642/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (3800061/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ) + (2:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb5 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (8:ℝ)*s)*x := by
    have he (y : ℝ) : (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (8:ℝ)*s)*y = ((-5:ℝ) + (8:ℝ)*s)*y+((-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (8:ℝ)*s)*(85/(153*s+7)) = ((397/2:ℝ) + (-527/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (397/2:ℝ) + (-527/2:ℝ)*s := by
        have h₀ : 0 ≤ (208080/7:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (36414:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (46818/7:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (8:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (8:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((1233/2:ℝ) + (-3667/2:ℝ)*s + (1377:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (1233/2:ℝ) + (-3667/2:ℝ)*s + (1377:ℝ)*s^2 := by
        have h₀ : 0 ≤ (5042880/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (10944702/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (5969295/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (8:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb6 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*x := by
    have he (y : ℝ) : (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*y = ((-5:ℝ) + (6:ℝ)*s)*y+((0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) = ((-170:ℝ) + (255:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-170:ℝ) + (255:ℝ)*s := by
        have h₀ : 0 ≤ (6866640/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (14825700/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (7959060/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((985:ℝ) + (-2763:ℝ)*s + (1938:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (985:ℝ) + (-2763:ℝ)*s + (1938:ℝ)*s^2 := by
        have h₀ : 0 ≤ (554880/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (1536732/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1076814/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (0:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb7 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*x := by
    have he (y : ℝ) : (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*y = ((-4:ℝ) + (6:ℝ)*s)*y+((-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) = ((-545/6:ℝ) + (255/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-545/6:ℝ) + (255/2:ℝ)*s := by
        have h₀ : 0 ≤ (1248480/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (3043170/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1794690/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((4457/6:ℝ) + (-13435/6:ℝ)*s + (1683:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (4457/6:ℝ) + (-13435/6:ℝ)*s + (1683:ℝ)*s^2 := by
        have h₀ : 0 ≤ (2660160/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (6377754/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (3800061/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-5/6:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb8 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*x := by
    have he (y : ℝ) : (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*y = ((-8:ℝ) + (12:ℝ)*s)*y+((-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*(85/(153*s+7)) = ((-113/2:ℝ) + (153/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-113/2:ℝ) + (153/2:ℝ)*s := by
        have h₀ : 0 ≤ (0:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (46818/7:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (46818/7:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((2721/2:ℝ) + (-8099/2:ℝ)*s + (3009:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (2721/2:ℝ) + (-8099/2:ℝ)*s + (3009:ℝ)*s^2 := by
        have h₀ : 0 ≤ (4128960/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (9950814/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (5969295/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-2:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb9 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-1/8:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*x := by
    have he (y : ℝ) : (-1/8:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*y = ((-5:ℝ) + (6:ℝ)*s)*y+((-1/8:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-1/8:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) = ((-227/2:ℝ) + (357/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-227/2:ℝ) + (357/2:ℝ)*s := by
        have h₀ : 0 ≤ (6866640/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (14497974/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (7631334/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-1/8:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-1/8:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((1857/2:ℝ) + (-5147/2:ℝ)*s + (1785:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (1857/2:ℝ) + (-5147/2:ℝ)*s + (1785:ℝ)*s^2 := by
        have h₀ : 0 ≤ (554880/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (1380366/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (912951/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-1/8:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-5:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb10 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-23/24:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*x := by
    have he (y : ℝ) : (-23/24:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*y = ((-4:ℝ) + (6:ℝ)*s)*y+((-23/24:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-23/24:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) = ((-103/3:ℝ) + (51:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-103/3:ℝ) + (51:ℝ)*s := by
        have h₀ : 0 ≤ (1248480/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (2715444/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1466964/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-23/24:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-23/24:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((2059/3:ℝ) + (-6149/3:ℝ)*s + (1530:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (2059/3:ℝ) + (-6149/3:ℝ)*s + (1530:ℝ)*s^2 := by
        have h₀ : 0 ≤ (2660160/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (6221388/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (3636198/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-23/24:ℝ)+(49/40:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb11 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-17/8:ℝ)+(109/40:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*x := by
    have he (y : ℝ) : (-17/8:ℝ)+(109/40:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*y = ((-8:ℝ) + (12:ℝ)*s)*y+((-17/8:ℝ)+(109/40:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-17/8:ℝ)+(109/40:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*(85/(153*s+7)) = ((0:ℝ))/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (0:ℝ) := by
        norm_num
      have hh : 0 ≤ (-17/8:ℝ)+(109/40:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-17/8:ℝ)+(109/40:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((1304:ℝ) + (-3860:ℝ)*s + (2856:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (1304:ℝ) + (-3860:ℝ)*s + (2856:ℝ)*s^2 := by
        have h₀ : 0 ≤ (4128960/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (9794448/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (5805432/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-17/8:ℝ)+(109/40:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (12:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb12 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-2:ℝ)+(4:ℝ)*(255*(1-s)/(153*s+7))+((-12:ℝ) + (16:ℝ)*s)*x := by
    have he (y : ℝ) : (-2:ℝ)+(4:ℝ)*(255*(1-s)/(153*s+7))+((-12:ℝ) + (16:ℝ)*s)*y = ((-12:ℝ) + (16:ℝ)*s)*y+((-2:ℝ)+(4:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-2:ℝ)+(4:ℝ)*(255*(1-s)/(153*s+7))+((-12:ℝ) + (16:ℝ)*s)*(85/(153*s+7)) = ((-14:ℝ) + (34:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-14:ℝ) + (34:ℝ)*s := by
        have h₀ : 0 ≤ (4161600/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (8468856/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (4307256/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-2:ℝ)+(4:ℝ)*(255*(1-s)/(153*s+7))+((-12:ℝ) + (16:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-2:ℝ)+(4:ℝ)*(255*(1-s)/(153*s+7))+((-12:ℝ) + (16:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((1970:ℝ) + (-5526:ℝ)*s + (3876:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (1970:ℝ) + (-5526:ℝ)*s + (3876:ℝ)*s^2 := by
        have h₀ : 0 ≤ (1109760/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (3073464/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2153628/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-2:ℝ)+(4:ℝ)*(255*(1-s)/(153*s+7))+((-12:ℝ) + (16:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb13 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-2:ℝ)+(2:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*x := by
    have he (y : ℝ) : (-2:ℝ)+(2:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*y = ((-9:ℝ) + (14:ℝ)*s)*y+((-2:ℝ)+(2:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-2:ℝ)+(2:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*(85/(153*s+7)) = ((-269:ℝ) + (374:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-269:ℝ) + (374:ℝ)*s := by
        have h₀ : 0 ≤ (2705040/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (7012296/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (4307256/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-2:ℝ)+(2:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-2:ℝ)+(2:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((1736:ℝ) + (-5336:ℝ)*s + (4080:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (1736:ℝ) + (-5336:ℝ)*s + (4080:ℝ)*s^2 := by
        have h₀ : 0 ≤ (7703040/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (18364896/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (10861776/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-2:ℝ)+(2:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb14 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-3:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (14:ℝ)*s)*x := by
    have he (y : ℝ) : (-3:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (14:ℝ)*s)*y = ((-8:ℝ) + (14:ℝ)*s)*y+((-3:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-3:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (14:ℝ)*s)*(85/(153*s+7)) = ((-127/2:ℝ) + (187/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-127/2:ℝ) + (187/2:ℝ)*s := by
        have h₀ : 0 ≤ (2080800/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (4562154/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2481354/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-3:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (14:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-3:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (14:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((2735/2:ℝ) + (-8813/2:ℝ)*s + (3519:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (2735/2:ℝ) + (-8813/2:ℝ)*s + (3519:ℝ)*s^2 := by
        have h₀ : 0 ≤ (12191040/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (27772866/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (15754257/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-3:ℝ)+(5/2:ℝ)*(255*(1-s)/(153*s+7))+((-8:ℝ) + (14:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb15 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-9/4:ℝ)+(29/12:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*x := by
    have he (y : ℝ) : (-9/4:ℝ)+(29/12:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*y = ((-9:ℝ) + (14:ℝ)*s)*y+((-9/4:ℝ)+(29/12:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-9/4:ℝ)+(29/12:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*(85/(153*s+7)) = ((-329/2:ℝ) + (459/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-329/2:ℝ) + (459/2:ℝ)*s := by
        have h₀ : 0 ≤ (1872720/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (4728618/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2855898/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-9/4:ℝ)+(29/12:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-9/4:ℝ)+(29/12:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((3263/2:ℝ) + (-9965/2:ℝ)*s + (3791:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (3263/2:ℝ) + (-9965/2:ℝ)*s + (3791:ℝ)*s^2 := by
        have h₀ : 0 ≤ (7305920/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (17256258/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (10136097/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-9/4:ℝ)+(29/12:ℝ)*(255*(1-s)/(153*s+7))+((-9:ℝ) + (14:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  have hb16 (x : ℝ) (hx : (85/(153*s+7)) ≤ x) (hx' : x ≤ ((408*s-248)/((153*s+7)*(2*s-1)))) : 0 ≤ (-1:ℝ)+(5/4:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*x := by
    have he (y : ℝ) : (-1:ℝ)+(5/4:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*y = ((-4:ℝ) + (6:ℝ)*s)*y+((-1:ℝ)+(5/4:ℝ)*(255*(1-s)/(153*s+7))) := by ring
    rw [he]
    apply affine_nonneg_between hx hx'
    ·
      have hid : (-1:ℝ)+(5/4:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) = ((-113/4:ℝ) + (153/4:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-113/4:ℝ) + (153/4:ℝ)*s := by
        have h₀ : 0 ≤ (0:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (23409/7:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (23409/7:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-1:ℝ)+(5/4:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
    ·
      have hid : (-1:ℝ)+(5/4:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) = ((2721/4:ℝ) + (-8099/4:ℝ)*s + (3009/2:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (2721/4:ℝ) + (-8099/4:ℝ)*s + (3009/2:ℝ)*s^2 := by
        have h₀ : 0 ≤ (2064480/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (4975407/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (5969295/98:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-1:ℝ)+(5/4:ℝ)*(255*(1-s)/(153*s+7))+((-4:ℝ) + (6:ℝ)*s)*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      nlinarith only [hh]
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    p_identity := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
    mean_identity := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
    a_low := by
      have hid : (-69/100:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((1:ℝ))*(85/(153*s+7)) = ((8017/100:ℝ) + (-10557/100:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (8017/100:ℝ) + (-10557/100:ℝ)*s := by
        have h₀ : 0 ≤ (4119984/245:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (29893293/1225:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (9293373/1225:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-69/100:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((1:ℝ))*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    a_high := by
      have hid : (4/5:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*(85/(153*s+7)) = ((-397/5:ℝ) + (612/5:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-397/5:ℝ) + (612/5:ℝ)*s := by
        have h₀ : 0 ≤ (4119984/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (43821648/245:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (23221728/245:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (4/5:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    p_low := by
      have hid : (-1/2:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((0:ℝ))*(85/(153*s+7)) = ((503/2:ℝ) + (-663/2:ℝ)*s)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (503/2:ℝ) + (-663/2:ℝ)*s := by
        have h₀ : 0 ≤ (2496960/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (3573774/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1076814/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (-1/2:ℝ)+(1:ℝ)*(255*(1-s)/(153*s+7))+((0:ℝ))*(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_low := by
      have hid : ((408*s-248)/((153*s+7)*(2*s-1)))-(85/(153*s+7)) = ((-163:ℝ) + (238:ℝ)*s)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-163:ℝ) + (238:ℝ)*s := by
        have h₀ : 0 ≤ (4785840/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (10591272/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (5805432/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ ((408*s-248)/((153*s+7)*(2*s-1)))-(85/(153*s+7)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_high := by
      have hid : (1:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*((408*s-248)/((153*s+7)*(2*s-1))) = ((241:ℝ) + (-547:ℝ)*s + (306:ℝ)*s^2)/((153*s+7)*(2*s-1)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (241:ℝ) + (-547:ℝ)*s + (306:ℝ)*s^2 := by
        have h₀ : 0 ≤ (1468800/49:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (2530620/49:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (1076814/49:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (1:ℝ)+(0:ℝ)*(255*(1-s)/(153*s+7))+((-1:ℝ))*((408*s-248)/((153*s+7)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    typeII := by
      have hid : (255*(1-s)/(153*s+7))-(2-2*s+1/50) = ((12043/50:ℝ) + (-27503/50:ℝ)*s + (306:ℝ)*s^2)/(153*s+7) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (12043/50:ℝ) + (-27503/50:ℝ)*s + (306:ℝ)*s^2 := by
        have h₀ : 0 ≤ (2849472/245:ℝ)*((3/4:ℝ)-s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (17992494/1225:ℝ)*((s-(113/153:ℝ))*((3/4:ℝ)-s)) := mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (4119984/1225:ℝ)*(s-(113/153:ℝ))^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (255*(1-s)/(153*s+7))-(2-2*s+1/50) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    budgets := by
      intro x hx hx'
      dsimp only
      have h0 := hb0 x hx hx'
      have h1 := hb1 x hx hx'
      have h2 := hb2 x hx hx'
      have h3 := hb3 x hx hx'
      have h4 := hb4 x hx hx'
      have h5 := hb5 x hx hx'
      have h6 := hb6 x hx hx'
      have h7 := hb7 x hx hx'
      have h8 := hb8 x hx hx'
      have h9 := hb9 x hx hx'
      have h10 := hb10 x hx hx'
      have h11 := hb11 x hx hx'
      have h12 := hb12 x hx hx'
      have h13 := hb13 x hx hx'
      have h14 := hb14 x hx hx'
      have h15 := hb15 x hx hx'
      have h16 := hb16 x hx hx'
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · unfold thirdAmplifierExponent
        apply max_le (by nlinarith only [h0])
        exact max_le (by nlinarith only [h1]) (by nlinarith only [h2])
      · unfold thirdAmplifierExponent
        apply max_le (by nlinarith only [h3])
        exact max_le (by nlinarith only [h4]) (by nlinarith only [h5])
      · unfold thirdAmplifierExponent
        apply max_le (by nlinarith only [h6])
        exact max_le (by nlinarith only [h7]) (by nlinarith only [h8])
      · unfold thirdAmplifierExponent
        apply max_le (by nlinarith only [h9])
        exact max_le (by nlinarith only [h10]) (by nlinarith only [h11])
      · nlinarith only [h12]
      · nlinarith only [h13]
      · nlinarith only [h14]
      · nlinarith only [h15]
      · nlinarith only [h16]
  }

end Montgomery.RationalMoment
