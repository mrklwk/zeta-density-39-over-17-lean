module
public import GuthMaynard.Improvement.UnequalFullInput

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff
namespace GuthMaynard.Improvement
open RiemannZeta.GuthMaynard

/-- Literal supremum norm for ordinary real inputs. For the compact smooth
inputs of the endpoint, boundedness and agreement with the Schwartz
order-zero seminorm are proved below. -/
def sourceSup (f : ℝ → ℝ) : ℝ := sSup (Set.range (fun x => |f x|))

def FourierSupInput (D : ℝ → ℕ → ℝ) (T : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ n : ℕ, ∀ ξ : ℝ, ξ ≠ 0 →
    ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ≤ D β n*T^β*(T/|ξ|)^n*sourceSup f

theorem sourceSup_eq_seminorm (f : 𝓢(ℝ, ℝ)) :
    sourceSup f = SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) := by
  have hbound : ∀ x, |f x| ≤ SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f) := by
    intro x
    simpa only [gmAffineComplexify_apply,Complex.norm_real,Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm (𝕜 := ℝ) (gmAffineComplexify f) x
  have hbdd : BddAbove (Set.range (fun x => |f x|)) :=
    ⟨_,by rintro y ⟨x,rfl⟩; exact hbound x⟩
  have hle : ∀ x, |f x| ≤ sourceSup f := fun x => le_csSup hbdd (mem_range_self x)
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro y ⟨x,rfl⟩; exact hbound x)
  · apply SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) 0 0 _ ((abs_nonneg (f 0)).trans (hle 0))
    intro x
    simpa only [pow_zero,iteratedDeriv_zero,one_mul,gmAffineComplexify_apply,Complex.norm_real,Real.norm_eq_abs] using hle x

/-- All integer triples in the closed real dyadic box. The surrounding
finite intervals are only a finite implementation, not additional cutoffs. -/
def affineBoxIndices (R K C₀ : ℝ) : Finset (ℤ × (ℤ × ℤ)) := by
  classical
  exact ((Finset.Icc (-⌈2*R⌉) ⌈2*R⌉).product
    ((Finset.Icc (-⌈2*K⌉) ⌈2*K⌉).product
      (Finset.Icc (-⌈C₀*R⌉) ⌈C₀*R⌉))).filter (InAffineBox R K C₀)

theorem mem_affineBoxIndices {R K C₀ : ℝ} (hK : 0 ≤ K) (p : ℤ × (ℤ × ℤ)) :
    p ∈ affineBoxIndices R K C₀ ↔ InAffineBox R K C₀ p := by
  classical
  unfold affineBoxIndices
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    refine Finset.mem_filter.mpr ⟨?_,hp⟩
    obtain ⟨hb1,hb2,hq1,hq2,hd⟩ := hp
    have hb := abs_le.mp (hb2.trans (Int.le_ceil (2*R)))
    have hqabs : |(p.2.1:ℝ)| ≤ (⌈2*K⌉:ℤ) := by
      rw [abs_of_nonneg (hK.trans hq1)]
      exact hq2.trans (Int.le_ceil _)
    have hq := abs_le.mp hqabs
    have hd' := abs_le.mp (hd.trans (Int.le_ceil (C₀*R)))
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast hb.1
      · exact_mod_cast hb.2
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · exact_mod_cast hq.1
        · exact_mod_cast hq.2
      · apply Finset.mem_Icc.mpr
        constructor
        · exact_mod_cast hd'.1
        · exact_mod_cast hd'.2


/-- The actual unequal affine square average, with precise
closed-shell convention R<=|b|<=2R, K<=q<=2K, |d|<=C₀R. -/
def affineAverage (R K C₀ : ℝ) (f : ℝ → ℝ) : ℝ :=
  affineIndexIntegral f (affineBoxIndices R K C₀)

/-- The full strengthened unequal-scale affine theorem. The fixed positive
support interval, fixed translation allowance and fixed Fourier constants
precede epsilon. The conclusion constant precedes all real T,R,K and all
ordinary smooth inputs. There is no Schwartz, smoothing, mass-profile,
integer-scale or tail-estimate premise. -/
theorem strengthened_unequal_affine
    (a b C₀ : ℝ) (ha : 0 < a) (hab : a ≤ b) (hC₀ : 0 ≤ C₀)
    (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K : ℝ) (f : ℝ → ℝ),
      2 ≤ T → 1 ≤ K → K ≤ R → R ≤ T^4 →
      ContDiff ℝ ∞ f → (∀ x, 0 ≤ f x) →
      (∀ x, x ∉ Icc a b → f x = 0) → FourierSupInput D T f →
      affineAverage R K C₀ f ≤ C*T^ε*
        (R^2*K^4*(∫ x, f x)^2+R*K^3*(∫ x, f x^2)) := by
  let L := ⌈b⌉₊
  have hL : 0 < L := Nat.ceil_pos.mpr (ha.trans_le hab)
  have hbL : b ≤ (L:ℝ) := Nat.le_ceil _
  obtain ⟨C,hC,h⟩ := unequal_affine_full_finite D hD L hL C₀ hC₀ hε
  refine ⟨C,hC,?_⟩
  intro T R K f hT hK hKR hRT hfd hf hs hp
  have hc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc hs
  let fs : 𝓢(ℝ, ℝ) := hc.toSchwartzMap hfd
  have hfs : GMAffineSupportedOn 0 L fs := by
    intro x hx
    apply hs
    intro habx
    exact hx ⟨ha.le.trans habx.1,habx.2.trans hbL⟩
  have hfp : FourierSupFamily D T fs := by
    intro β hβ n ξ hξ
    have hh := hp β hβ n ξ hξ
    rw [show sourceSup f = SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify fs) from sourceSup_eq_seminorm fs] at hh
    exact hh
  exact h T R K fs (affineBoxIndices R K C₀) hT hK hKR hRT hf hfs hfp
    (fun p hp => (mem_affineBoxIndices (by linarith) p).mp hp)

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.sourceSup_eq_seminorm
#print axioms GuthMaynard.Improvement.mem_affineBoxIndices
#print axioms GuthMaynard.Improvement.strengthened_unequal_affine
