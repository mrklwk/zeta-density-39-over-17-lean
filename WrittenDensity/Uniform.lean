module
public import WrittenDensity.UniformModulus

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.WrittenDensity
open MathCollab.Density
/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_A_1 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/10) ≤ σ → σ ≤ (12/17) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((6+-6*σ)/(-3+8*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(7/10)) (b:=(12/17)) (K:=31)
    (f:=fun σ : ℝ => ((6+-6*σ)/(-3+8*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=6) (b:=-6) (c:=-3) (d:=8)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((6+-6*σ)/(-3+8*σ)) ε
    simpa using source_v7_A_1 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_A_2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (12/17) ≤ σ → σ ≤ (81/113) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((54+-54*σ)/(-15+55*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(12/17)) (b:=(81/113)) (K:=2161)
    (f:=fun σ : ℝ => ((54+-54*σ)/(-15+55*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=54) (b:=-54) (c:=-15) (d:=55)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((54+-54*σ)/(-15+55*σ)) ε
    simpa using source_v7_A_2 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_A_3 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (81/113) ≤ σ → σ ≤ (47/65) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((414+-414*σ)/(-7+271*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(81/113)) (b:=(47/65)) (K:=109297)
    (f:=fun σ : ℝ => ((414+-414*σ)/(-7+271*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=414) (b:=-414) (c:=-7) (d:=271)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((414+-414*σ)/(-7+271*σ)) ε
    simpa using source_v7_A_3 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_A_4 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (47/65) ≤ σ → σ ≤ (69/91) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((39+-39*σ)/(-1+26*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(47/65)) (b:=(69/91)) (K:=976)
    (f:=fun σ : ℝ => ((39+-39*σ)/(-1+26*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=39) (b:=-39) (c:=-1) (d:=26)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((39+-39*σ)/(-1+26*σ)) ε
    simpa using source_v7_A_4 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_A_5 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (69/91) ≤ σ → σ ≤ (7/9) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((12+-12*σ)/(5+1*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(69/91)) (b:=(7/9)) (K:=73)
    (f:=fun σ : ℝ => ((12+-12*σ)/(5+1*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=12) (b:=-12) (c:=5) (d:=1)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((12+-12*σ)/(5+1*σ)) ε
    simpa using source_v7_A_5 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_B_1 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (69/91) ≤ σ → σ ≤ (63/83) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((3+-3*σ)/(-16+23*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(69/91)) (b:=(63/83)) (K:=22)
    (f:=fun σ : ℝ => ((3+-3*σ)/(-16+23*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=3) (b:=-3) (c:=-16) (d:=23)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((3+-3*σ)/(-16+23*σ)) ε
    simpa using source_v7_B_1 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_B_2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (63/83) ≤ σ → σ ≤ (45/59) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((12+-12*σ)/(-1+9*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(63/83)) (b:=(45/59)) (K:=97)
    (f:=fun σ : ℝ => ((12+-12*σ)/(-1+9*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=12) (b:=-12) (c:=-1) (d:=9)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((12+-12*σ)/(-1+9*σ)) ε
    simpa using source_v7_B_2 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_B_3 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (45/59) ≤ σ → σ ≤ (13/17) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((6+-6*σ)/(-23+34*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(45/59)) (b:=(13/17)) (K:=67)
    (f:=fun σ : ℝ => ((6+-6*σ)/(-23+34*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=6) (b:=-6) (c:=-23) (d:=34)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((6+-6*σ)/(-23+34*σ)) ε
    simpa using source_v7_B_3 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_B_4 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (13/17) ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((2+-2*σ)/(1+0*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(13/17)) (b:=1) (K:=3)
    (f:=fun σ : ℝ => ((2+-2*σ)/(1+0*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=2) (b:=-2) (c:=1) (d:=0)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((2+-2*σ)/(1+0*σ)) ε
    simpa using source_v7_B_4 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_C_1 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (43/56) ≤ σ → σ ≤ (11/14) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((3+-3*σ)/(0+2*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(43/56)) (b:=(11/14)) (K:=7)
    (f:=fun σ : ℝ => ((3+-3*σ)/(0+2*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=3) (b:=-3) (c:=0) (d:=2)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((3+-3*σ)/(0+2*σ)) ε
    unfold DensityBound
    have he : (3:ℝ)*(1-σ)/(2*σ) = ((3+-3*σ)/(0+2*σ)) := by ring
    simpa only [he] using MathCollab.Density.Stronger.stronger_density_bound_native (by linarith : (3/4:ℝ)<σ) hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_C_2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (11/14) ≤ σ → σ ≤ (5/6) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((4+-4*σ)/(-1+4*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(11/14)) (b:=(5/6)) (K:=13)
    (f:=fun σ : ℝ => ((4+-4*σ)/(-1+4*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=4) (b:=-4) (c:=-1) (d:=4)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((4+-4*σ)/(-1+4*σ)) ε
    simpa using source_v7_C_2 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_C_3 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (5/6) ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((6+-6*σ)/(1+3*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(5/6)) (b:=1) (K:=25)
    (f:=fun σ : ℝ => ((6+-6*σ)/(1+3*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=6) (b:=-6) (c:=1) (d:=3)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((6+-6*σ)/(1+3*σ)) ε
    by_cases h : σ < 1
    ·
      simpa using source_v7_C_3 hlo h hε
    · exact density_of_actual_zero (by linarith)
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_D1_1 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (5/6) ≤ σ → σ ≤ (67/80) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((4+-4*σ)/(-1+4*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(5/6)) (b:=(67/80)) (K:=13)
    (f:=fun σ : ℝ => ((4+-4*σ)/(-1+4*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=4) (b:=-4) (c:=-1) (d:=4)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((4+-4*σ)/(-1+4*σ)) ε
    simpa using source_v7_D1_1 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_D1_2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (67/80) ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((39+-39*σ)/(7+19*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(67/80)) (b:=1) (K:=1015)
    (f:=fun σ : ℝ => ((39+-39*σ)/(7+19*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=39) (b:=-39) (c:=7) (d:=19)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((39+-39*σ)/(7+19*σ)) ε
    by_cases h : σ < 1
    ·
      simpa using source_v7_D1_2 hlo h hε
    · exact density_of_actual_zero (by linarith)
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_D2_1 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (6/7) ≤ σ → σ ≤ (69/80) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((39+-39*σ)/(-27+59*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(6/7)) (b:=(69/80)) (K:=1249)
    (f:=fun σ : ℝ => ((39+-39*σ)/(-27+59*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=39) (b:=-39) (c:=-27) (d:=59)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((39+-39*σ)/(-27+59*σ)) ε
    simpa using source_v7_D2_1 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_D2_2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (69/80) ≤ σ → σ ≤ (51/58) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((4+-4*σ)/(-1+4*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(69/80)) (b:=(51/58)) (K:=13)
    (f:=fun σ : ℝ => ((4+-4*σ)/(-1+4*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=4) (b:=-4) (c:=-1) (d:=4)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((4+-4*σ)/(-1+4*σ)) ε
    simpa using source_v7_D2_2 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_D2_3 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (51/58) ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((42+-42*σ)/(15+13*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(51/58)) (b:=1) (K:=1177)
    (f:=fun σ : ℝ => ((42+-42*σ)/(15+13*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=42) (b:=-42) (c:=15) (d:=13)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((42+-42*σ)/(15+13*σ)) ε
    by_cases h : σ < 1
    ·
      simpa using source_v7_D2_3 hlo h hε
    · exact density_of_actual_zero (by linarith)
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_coprime_cubic {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (37/50) ≤ σ → σ ≤ (315/418) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((333+-333*σ)/(-12+227*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(37/50)) (b:=(315/418)) (K:=71596)
    (f:=fun σ : ℝ => ((333+-333*σ)/(-12+227*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=333) (b:=-333) (c:=-12) (d:=227)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((333+-333*σ)/(-12+227*σ)) ε
    simpa using source_v7_coprime_cubic hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_coprime_quadratic {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (201+Real.sqrt 145)/272 ≤ σ → σ ≤ (9/10) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((4+-4*σ)/(-1+4*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(201+Real.sqrt 145)/272) (b:=(9/10)) (K:=13)
    (f:=fun σ : ℝ => ((4+-4*σ)/(-1+4*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have hxR := source_transition_endpoint_bounds.1.trans hx
    have h := linear_fraction_modulus (a:=4) (b:=-4) (c:=-1) (d:=4)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((4+-4*σ)/(-1+4*σ)) ε
    simpa using source_v7_coprime_quadratic hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_transition_first {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (13/17) ≤ σ → σ ≤ (23/30) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((36+-44*σ)/(31+-34*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(13/17)) (b:=(23/30)) (K:=141)
    (f:=fun σ : ℝ => ((36+-44*σ)/(31+-34*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=36) (b:=-44) (c:=31) (d:=-34)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((36+-44*σ)/(31+-34*σ)) ε
    have hneg : (-31 + (34 * σ)) ≠ 0 := by linarith
    have hpos : (31+-34*σ) ≠ 0 := by linarith
    have he : ((-36 + (44 * σ)) / (-31 + (34 * σ))) = ((36+-44*σ)/(31+-34*σ)) := by
      apply (div_eq_div_iff hneg hpos).2
      ring
    simpa only [he] using source_v7_transition_first hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_transition_second {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/9) ≤ σ → σ ≤ (201+Real.sqrt 145)/272 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((18+-21*σ)/(14+-13*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(7/9)) (b:=(201+Real.sqrt 145)/272) (K:=61)
    (f:=fun σ : ℝ => ((18+-21*σ)/(14+-13*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have hyR := hy.trans source_transition_endpoint_bounds.2
    have h := linear_fraction_modulus (a:=18) (b:=-21) (c:=14) (d:=-13)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((18+-21*σ)/(14+-13*σ)) ε
    have hhiR := hhi.trans source_transition_endpoint_bounds.2
    have hneg : (-14 + (13 * σ)) ≠ 0 := by linarith
    have hpos : (14+-13*σ) ≠ 0 := by linarith
    have he : ((-18 + (21 * σ)) / (-14 + (13 * σ))) = ((18+-21*σ)/(14+-13*σ)) := by
      apply (div_eq_div_iff hneg hpos).2
      ring
    simpa only [he] using source_v7_transition_second hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_power_first {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (57/80) ≤ σ → σ ≤ (5/7) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((651+-651*σ)/(-25+446*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(57/80)) (b:=(5/7)) (K:=274072)
    (f:=fun σ : ℝ => ((651+-651*σ)/(-25+446*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=651) (b:=-651) (c:=-25) (d:=446)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((651+-651*σ)/(-25+446*σ)) ε
    simpa using source_v7_power_first hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_v7_power_second {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (37/50) ≤ σ → σ ≤ (3/4) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((192+-192*σ)/(-7+131*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(37/50)) (b:=(3/4)) (K:=23809)
    (f:=fun σ : ℝ => ((192+-192*σ)/(-7+131*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=192) (b:=-192) (c:=-7) (d:=131)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((192+-192*σ)/(-7+131*σ)) ε
    simpa using source_v7_power_second hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_oct2_mixed_1 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (4/5) ≤ σ → σ ≤ (417/514) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((121+-121*σ)/(-35+127*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(4/5)) (b:=(417/514)) (K:=11133)
    (f:=fun σ : ℝ => ((121+-121*σ)/(-35+127*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=121) (b:=-121) (c:=-35) (d:=127)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((121+-121*σ)/(-35+127*σ)) ε
    simpa using source_oct2_mixed_1 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_oct2_mixed_2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (417/514) ≤ σ → σ ≤ (161/194) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((116+-116*σ)/(-37+126*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(417/514)) (b:=(161/194)) (K:=10325)
    (f:=fun σ : ℝ => ((116+-116*σ)/(-37+126*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=116) (b:=-116) (c:=-37) (d:=126)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((116+-116*σ)/(-37+126*σ)) ε
    simpa using source_oct2_mixed_2 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_oct2_mixed_3 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (161/194) ≤ σ → σ ≤ (19/22) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((27+-27*σ)/(-10+31*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(161/194)) (b:=(19/22)) (K:=568)
    (f:=fun σ : ℝ => ((27+-27*σ)/(-10+31*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=27) (b:=-27) (c:=-10) (d:=31)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((27+-27*σ)/(-10+31*σ)) ε
    simpa using source_oct2_mixed_3 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_oct2_mixed_4 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22) ≤ σ → σ ≤ (23/26) → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((24+-24*σ)/(-11+30*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(19/22)) (b:=(23/26)) (K:=457)
    (f:=fun σ : ℝ => ((24+-24*σ)/(-11+30*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=24) (b:=-24) (c:=-11) (d:=30)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((24+-24*σ)/(-11+30*σ)) ε
    simpa using source_oct2_mixed_4 hlo hhi hε
  · exact hε

/-- One constant precedes sigma and height on the full closed source interval. Open printed upper endpoints may be restricted afterward. Original analytic routes remain separate. -/
theorem uniform_source_oct2_mixed_5 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26) ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(((6+-6*σ)/(3+1*σ))+ε) := by
  apply GuthMaynard.Improvement.density_curve_uniform_on_interval
    (a:=(23/26)) (b:=1) (K:=25)
    (f:=fun σ : ℝ => ((6+-6*σ)/(3+1*σ)))
  · linarith [source_transition_endpoint_bounds.1,source_transition_endpoint_bounds.2]
  · norm_num
  · intro x y hx hxy hy
    have h := linear_fraction_modulus (a:=6) (b:=-6) (c:=3) (d:=1)
      hxy (by linarith) (by linarith) (by norm_num)
    norm_num at h
    simpa using h
  · intro σ hlo hhi ε hε
    change DensityBound σ ((6+-6*σ)/(3+1*σ)) ε
    by_cases h : σ < 1
    ·
      simpa using source_oct2_mixed_5 hlo h hε
    · exact density_of_actual_zero (by linarith)
  · exact hε

end Montgomery.WrittenDensity
