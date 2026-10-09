module
public import GuthMaynard.Improvement.ReflectedBandMeanValue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- The exact natural lengths retain the short reflected-band scale. -/
theorem reflected_band_length_bounds {N L H : ℝ} (hN : 2 ≤ N) (hNL : N ≤ L)
    (hH : 0 < H) :
    let X := reflectedBandLength L H
    let Y := ⌊2*N⌋₊*X
    (X:ℝ)*L ≤ 2*H ∧ N*X ≤ 2*H ∧ (Y:ℝ) ≤ 4*H := by
  have hL : 0 < L := by linarith
  let X := reflectedBandLength L H
  have hx : (X:ℝ) ≤ 4*H/(Real.pi*L) := Nat.floor_le (by positivity)
  have hxp := (le_div_iff₀ (mul_pos Real.pi_pos hL)).mp hx
  have hxL : 0 ≤ (X:ℝ)*L := mul_nonneg (Nat.cast_nonneg _) hL.le
  have hbound : (X:ℝ)*L ≤ 2*H := by nlinarith [Real.pi_gt_three]
  have hnX : N*(X:ℝ) ≤ 2*H := by nlinarith [mul_le_mul_of_nonneg_right hNL (Nat.cast_nonneg X)]
  refine ⟨hbound,hnX,?_⟩
  have hf := Nat.floor_le (by positivity : 0 ≤ 2*N)
  have hh := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg X)
  push_cast
  change (⌊2*N⌋₊:ℝ)*(X:ℝ) ≤ _
  nlinarith

/-- Logarithmic loss in the actual product length, including zero length. -/
theorem reflected_band_log_budget {A p δ N H : ℝ} (hA : 1 ≤ A) (hp : 0 < p)
    (hδ : 0 < δ) (hN : 2 ≤ N) (hH : 0 ≤ H) (hupper : H ≤ A*N^p)
    (Y : ℕ) (hY : (Y:ℝ) ≤ 4*H) :
    H+4*(Y:ℝ)*(1+Real.log Y) ≤
      (1+16*(1+Real.log (4*A)+p/δ))*H*N^δ := by
  have hN0 : 0 < N := by linarith
  have hnδ : 1 ≤ N^δ := Real.one_le_rpow (by linarith) hδ.le
  have hlogA : 0 ≤ Real.log (4*A) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 1+Real.log (4*A)+p/δ := by positivity
  have hlog : 1+Real.log Y ≤ (1+Real.log (4*A)+p/δ)*N^δ := by
    by_cases hy : Y=0
    · simp only [hy,Nat.cast_zero,Real.log_zero,add_zero]
      nlinarith [div_nonneg hp.le hδ.le]
    · have hy0 : (0:ℝ) < Y := by exact_mod_cast Nat.pos_of_ne_zero hy
      have hh : (Y:ℝ) ≤ 4*A*N^p := by nlinarith
      have hlg := Real.log_le_log hy0 hh
      rw [Real.log_mul (by positivity : 4*A ≠ 0) (by positivity : N^p ≠ 0),Real.log_rpow hN0] at hlg
      have hlN := Real.log_le_rpow_div hN0.le hδ
      have hm := mul_le_mul_of_nonneg_left hlN hp.le
      rw [show p*(N^δ/δ)=(p/δ)*N^δ by ring] at hm
      have ha := mul_le_mul_of_nonneg_left hnδ (show 0 ≤ 1+Real.log (4*A) by positivity)
      nlinarith
  have hprod := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4*(Y:ℝ) by positivity)
  have hheight := mul_le_mul_of_nonneg_right hY (mul_nonneg hcoef (Real.rpow_nonneg hN0.le δ))
  nlinarith [mul_le_mul_of_nonneg_left hnδ hH]

/-- Uniform raw band-scale absorption for every fixed polynomial height range.
No lower shell condition H>=cL is required. -/
theorem reflected_band_raw_budget {ε A p : ℝ} (hε : 0 < ε) (hA : 1 ≤ A) (hp : 0 < p) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ N L H : ℝ,
      2 ≤ N → N ≤ L → 0 < H → H ≤ A*N^p →
      let X := reflectedBandLength L H
      let Y := ⌊2*N⌋₊*X
      (L^2/H)*(H+4*(Y:ℝ)*(1+Real.log Y))*(1+2*N*X)^η*(N+1)*X ≤
        C*N^ε*L*N*H := by
  let δ := ε/2
  let η := ε/(2*p)
  let B := 1+16*(1+Real.log (4*A)+p/δ)
  let C := 4*B*(5*A)^η
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hlogA : 0 ≤ Real.log (4*A) := Real.log_nonneg (by linarith)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨η,C,hη,by dsimp [C]; positivity,?_⟩
  intro N L H hN hNL hH hupper
  dsimp only
  let X := reflectedBandLength L H
  let Y := ⌊2*N⌋₊*X
  have hN0 : 0 < N := by linarith
  have hL : 0 < L := hN0.trans_le hNL
  obtain ⟨hx,hnx,hy⟩ := reflected_band_length_bounds hN hNL hH
  have hlog := reflected_band_log_budget hA hp hδ hN hH.le hupper Y hy
  have hNp : 1 ≤ N^p := Real.one_le_rpow (by linarith) hp.le
  have hbase : 1+2*N*X ≤ 5*A*N^p := by dsimp [X]; nlinarith
  have hpower : (1+2*N*X)^η ≤ (5*A)^η*N^(p*η) := by
    calc
      _ ≤ (5*A*N^p)^η := Real.rpow_le_rpow (by positivity) hbase hη.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hN0.le]
  have hxdiv : (X:ℝ) ≤ 2*H/L := (le_div_iff₀ hL).mpr hx
  have hNplus : N+1 ≤ 2*N := by linarith
  have he : δ+p*η=ε := by dsimp [δ,η]; field_simp; ring
  calc
    _ ≤ (L^2/H)*(B*H*N^δ)*((5*A)^η*N^(p*η))*(2*N)*(2*H/L) := by
      apply mul_le_mul
      · apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hlog (by positivity)
          · exact hpower
          · positivity
          · positivity
        · exact hNplus
        · positivity
        · positivity
      · exact hxdiv
      · positivity
      · positivity
    _ = C*N^ε*L*N*H := by
      have hpow : N^δ*N^(p*η)=N^ε := by rw [← Real.rpow_add hN0,he]
      dsimp [C]
      field_simp
      nlinarith [hpow]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.reflected_band_length_bounds
#print axioms GuthMaynard.Improvement.reflected_band_log_budget
#print axioms GuthMaynard.Improvement.reflected_band_raw_budget
