import GuthMaynard.Improvement.SourceRatioAssembly
set_option autoImplicit false
noncomputable section
open Finset
namespace GuthMaynard.Improvement

def sourceHeight (N T : ℝ) : ℝ := min (2*N) (max 2 (Real.sqrt T))

/-- The actual low-height threshold is positive, bounded by the source
height, and its square costs at most 2T. -/
theorem sourceHeight_bounds {N T : ℝ} (hN : 2 ≤ N) (hT : 2 ≤ T) :
    2 ≤ sourceHeight N T ∧ sourceHeight N T ≤ 2*N ∧
      (sourceHeight N T)^2 ≤ 2*T := by
  have hY : 2 ≤ sourceHeight N T := le_min (by linarith) (le_max_left _ _)
  refine ⟨hY,min_le_left _ _,?_⟩
  have hh : (max 2 (Real.sqrt T))^2 ≤ 2*T := by
    by_cases h : 2 ≤ Real.sqrt T
    · rw [max_eq_right h,Real.sq_sqrt (by linarith : 0 ≤ T)]
      linarith
    · rw [max_eq_left (by linarith)]
      nlinarith
  have hY0 : 0 ≤ sourceHeight N T := by linarith
  exact (sq_le_sq₀ hY0 (by positivity)).mpr (min_le_right _ _) |>.trans hh

/-- If high shells occur, their initial height is at least sqrt(T). -/
theorem sourceHeight_sqrt_le_of_lt {N T : ℝ}
    (h : sourceHeight N T < 2*N) : Real.sqrt T ≤ sourceHeight N T := by
  have he : sourceHeight N T=max 2 (Real.sqrt T) := by
    unfold sourceHeight at h ⊢
    rcases min_choice (2*N) (max 2 (Real.sqrt T)) with he | he
    · rw [he] at h
      exact False.elim (lt_irrefl _ h)
    · exact he
  rw [he]
  exact le_max_right _ _

/-- Actual least dyadic cover. Minimality yields the strict factor-two
overshoot and correctly makes the full-height case have zero shells. -/
theorem source_least_height_cover {X Y : ℝ} (hY : 0 < Y) (hYX : Y ≤ X) :
    ∃ J : ℕ, X ≤ (2:ℝ)^J*Y ∧ (∀ j < J, (2:ℝ)^j*Y < X) ∧
      (2:ℝ)^J*Y < 2*X ∧ (J=0 ↔ Y=X) := by
  have hex : ∃ j : ℕ, X ≤ (2:ℝ)^j*Y := by
    obtain ⟨j,hj⟩ := pow_unbounded_of_one_lt (X/Y) (by norm_num : (1:ℝ)<2)
    exact ⟨j,((div_lt_iff₀ hY).mp hj).le⟩
  let J := Nat.find hex
  have hcover : X ≤ (2:ℝ)^J*Y := Nat.find_spec hex
  have hmin : ∀ j < J, (2:ℝ)^j*Y < X := by
    intro j hj
    exact lt_of_not_ge (Nat.find_min hex hj)
  have hbound : (2:ℝ)^J*Y < 2*X := by
    cases hj : J with
    | zero => simp only [pow_zero,one_mul]; linarith
    | succ j =>
      have hh := hmin j (by omega)
      rw [pow_succ]
      nlinarith
  refine ⟨J,hcover,hmin,hbound,?_⟩
  constructor
  · intro hj
    simp only [hj,pow_zero,one_mul] at hcover
    exact le_antisymm hYX hcover
  · intro he
    have hh : Nat.find hex ≤ 0 := Nat.find_min' hex (by simp [he])
    exact Nat.le_zero.mp hh

/-- Exact positive geometric sum for the actual shell heights. -/
theorem source_height_geometric_sum (Y : ℝ) (J : ℕ) :
    (∑ j ∈ range J, (2:ℝ)^j*Y) = ((2:ℝ)^J-1)*Y := by
  induction J with
  | zero => simp
  | succ J ih => rw [sum_range_succ,ih,pow_succ]; ring

/-- Exact reciprocal geometric sum; no logarithmic shell-count loss. -/
theorem source_height_inverse_sum (Y : ℝ) (J : ℕ) :
    (∑ j ∈ range J, ((2:ℝ)^j*Y)⁻¹) = 2*Y⁻¹*(1-((2:ℝ)⁻¹)^J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ,ih,pow_succ]
    simp only [mul_inv_rev,inv_pow]
    ring

/-- Uniform low-height budget with the requested logarithmic factor. -/
theorem source_low_height_budget {N T : ℝ} (hN : 2 ≤ N) (hT : 2 ≤ T) :
    (T+(sourceHeight N T)^2)*Real.log (2*sourceHeight N T) ≤
      6*T*Real.log (2*N) := by
  obtain ⟨hY,hYN,hYsq⟩ := sourceHeight_bounds hN hT
  have hNp : 0 < N := by linarith
  have hYp : 0 < sourceHeight N T := by linarith
  have hlogN : 0 ≤ Real.log (2*N) := Real.log_nonneg (by linarith)
  have hlogY : 0 ≤ Real.log (2*sourceHeight N T) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2*sourceHeight N T) ≤ 2*Real.log (2*N) := by
    calc
      _ ≤ Real.log (2*(2*N)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2+Real.log (2*N) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by
        have hh : Real.log 2 ≤ Real.log (2*N) := Real.log_le_log (by norm_num) (by linarith)
        linarith
  calc
    _ ≤ (3*T)*(2*Real.log (2*N)) := mul_le_mul (by linarith) hlog hlogY (by linarith)
    _ = _ := by ring

/-- The high-height derivative loss is sqrt(T), whenever high shells exist. -/
theorem source_high_height_budget {N T : ℝ} (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hhigh : sourceHeight N T < 2*N) :
    N*T/sourceHeight N T ≤ N*Real.sqrt T := by
  have hY := (sourceHeight_bounds hN hT).1
  have hs := sourceHeight_sqrt_le_of_lt hhigh
  have hs2 := Real.sq_sqrt (by linarith : 0 ≤ T)
  apply (div_le_iff₀ (by linarith : 0 < sourceHeight N T)).mpr
  have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg T)
  nlinarith [mul_nonneg (show 0 ≤ N by linarith)
    (show 0 ≤ Real.sqrt T*sourceHeight N T-T by nlinarith)]

/-- One least cover simultaneously supplies both shell budgets and the
empty-high-range conclusion, with absolute constants 4 and 2. -/
theorem source_height_shell_budgets {N T : ℝ} (hN : 2 ≤ N) (hT : 2 ≤ T) :
    ∃ J : ℕ, 2*N ≤ (2:ℝ)^J*sourceHeight N T ∧
      (∀ j < J, (2:ℝ)^j*sourceHeight N T < 2*N) ∧
      (J=0 ↔ sourceHeight N T=2*N) ∧
      (∑ j ∈ range J, (2:ℝ)^j*sourceHeight N T) ≤ 4*N ∧
      (∑ j ∈ range J, ((2:ℝ)^j*sourceHeight N T)⁻¹) ≤ 2/sourceHeight N T := by
  obtain ⟨hY,hYN,_⟩ := sourceHeight_bounds hN hT
  obtain ⟨J,hcover,hmin,hbound,hzero⟩ := source_least_height_cover
    (by linarith : 0 < sourceHeight N T) hYN
  refine ⟨J,hcover,hmin,hzero,?_,?_⟩
  · rw [source_height_geometric_sum]
    nlinarith
  · rw [source_height_inverse_sum]
    have hp : 0 ≤ ((2:ℝ)⁻¹)^J := by positivity
    have hy : 0 ≤ (sourceHeight N T)⁻¹ := by positivity
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hy) hp]

theorem source_log_mass_ge_one {N : ℝ} (hN : 2 ≤ N) : 1 ≤ Real.log (2*N) := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hh
  have hlog : Real.log 4 ≤ Real.log (2*N) := Real.log_le_log (by norm_num) (by linarith)
  have he : Real.log 4=2*Real.log 2 := by
    have hx := Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)
    norm_num at hx
    linarith
  rw [he] at hlog
  linarith

/-- Scalar low-height Fourier cost, with all source quantities actual and
no sampling or variation estimate among the premises. -/
theorem source_sampling_low_scalar {N T c M : ℝ} (hN : 2 ≤ N) (hT : 2 ≤ T)
    (hc : 0 ≤ c) (hM : 0 ≤ M) :
    Real.sqrt (16*N^2*Real.log (2*N))*
      Real.sqrt ((2*Real.pi*(sourceHeight N T)^2+4*Real.pi*c*T)*M) ≤
      (8*Real.sqrt (Real.pi*(1+c)))*N*Real.sqrt (T*Real.log (2*N))*Real.sqrt M := by
  have hlog : 0 ≤ Real.log (2*N) := (by norm_num : (0:ℝ) ≤ 1).trans (source_log_mass_ge_one hN)
  have hT0 : 0 ≤ T := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hp : 0 ≤ Real.pi*(1+c) := by positivity
  have hY := (sourceHeight_bounds hN hT).2.2
  have hK : (2*Real.pi*(sourceHeight N T)^2+4*Real.pi*c*T)*M ≤
      4*Real.pi*(1+c)*T*M := by
    apply mul_le_mul_of_nonneg_right _ hM
    nlinarith [mul_le_mul_of_nonneg_left hY (show 0 ≤ 2*Real.pi by positivity)]
  have hW : 0 ≤ 16*N^2*Real.log (2*N) := by positivity
  have hK0 : 0 ≤ (2*Real.pi*(sourceHeight N T)^2+4*Real.pi*c*T)*M := by positivity
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt hW,Real.sq_sqrt hK0]
  calc
    _ ≤ (16*N^2*Real.log (2*N))*(4*Real.pi*(1+c)*T*M) := mul_le_mul_of_nonneg_left hK hW
    _ = _ := by
      simp only [mul_pow,Real.sq_sqrt hp,Real.sq_sqrt (mul_nonneg hT0 hlog),Real.sq_sqrt hM]
      ring

/-- Uniform scalar absorption for the actual low cost and both high-shell
costs. The high derivative term is literally absent when Y is the full height. -/
theorem source_sampling_scalar_budget (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N T M I : ℝ, 2 ≤ N → 2 ≤ T → 0 ≤ M → 0 ≤ I →
      Real.sqrt (16*N^2*Real.log (2*N))*
        Real.sqrt ((2*Real.pi*(sourceHeight N T)^2+4*Real.pi*c*T)*M) +
        64*Real.pi*N^2*I +
        (if sourceHeight N T=2*N then 0 else
          16*Real.pi*c*(N*T/sourceHeight N T)*Real.sqrt M) ≤
        C*(N^2*I+N*Real.sqrt (T*Real.log (2*N))*Real.sqrt M) := by
  let C := 64*Real.pi+8*Real.sqrt (Real.pi*(1+c))+16*Real.pi*c
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro N T M I hN hT hM hI
  let Z := N*Real.sqrt (T*Real.log (2*N))*Real.sqrt M
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hX : 0 ≤ N^2*I := by positivity
  have hl : Real.sqrt (16*N^2*Real.log (2*N))*
      Real.sqrt ((2*Real.pi*(sourceHeight N T)^2+4*Real.pi*c*T)*M) ≤
      (8*Real.sqrt (Real.pi*(1+c)))*Z := by
    simpa only [Z,mul_assoc] using source_sampling_low_scalar hN hT hc hM
  have hd : (if sourceHeight N T=2*N then 0 else
      16*Real.pi*c*(N*T/sourceHeight N T)*Real.sqrt M) ≤ (16*Real.pi*c)*Z := by
    split_ifs with he
    · positivity
    · have hh : sourceHeight N T < 2*N := lt_of_le_of_ne (sourceHeight_bounds hN hT).2.1 he
      have hroot : Real.sqrt T ≤ Real.sqrt (T*Real.log (2*N)) := by
        apply Real.sqrt_le_sqrt
        nlinarith [source_log_mass_ge_one hN]
      have hcost : (N*T/sourceHeight N T)*Real.sqrt M ≤ Z := by
        calc
          _ ≤ (N*Real.sqrt T)*Real.sqrt M :=
            mul_le_mul_of_nonneg_right (source_high_height_budget hN hT hh) (Real.sqrt_nonneg M)
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hroot (by linarith)) (Real.sqrt_nonneg M)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcost (show 0 ≤ 16*Real.pi*c by positivity)
  calc
    _ ≤ 64*Real.pi*(N^2*I)+(8*Real.sqrt (Real.pi*(1+c))+16*Real.pi*c)*Z := by nlinarith
    _ ≤ C*(N^2*I)+C*Z := add_le_add
      (mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [Real.sqrt_nonneg (Real.pi*(1+c)), mul_nonneg Real.pi_pos.le hc]) hX)
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [Real.pi_pos]) hZ)
    _ = _ := by dsimp [Z]; ring

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.sourceHeight_bounds
#print axioms GuthMaynard.Improvement.sourceHeight_sqrt_le_of_lt
#print axioms GuthMaynard.Improvement.source_least_height_cover
#print axioms GuthMaynard.Improvement.source_height_geometric_sum
#print axioms GuthMaynard.Improvement.source_height_inverse_sum
#print axioms GuthMaynard.Improvement.source_low_height_budget
#print axioms GuthMaynard.Improvement.source_high_height_budget
#print axioms GuthMaynard.Improvement.source_height_shell_budgets

#print axioms GuthMaynard.Improvement.source_log_mass_ge_one

#print axioms GuthMaynard.Improvement.source_sampling_low_scalar

#print axioms GuthMaynard.Improvement.source_sampling_scalar_budget
