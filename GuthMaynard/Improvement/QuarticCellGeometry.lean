module
public import GuthMaynard.Improvement.SourceQuarticKernel
public import GuthMaynard.Improvement.SeparatedLevelVolume

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

/-- Actual occupied integer cells, with witnesses inside the stated set. -/
def occupiedRealCells (S : Set ℝ) (a b : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc ⌊a⌋ ⌊b⌋).filter (fun k => ∃ x ∈ S, ⌊x⌋ = k)

theorem occupiedRealCells_mem {S : Set ℝ} {a b x : ℝ}
    (hS : S ⊆ Icc a b) (hx : x ∈ S) : ⌊x⌋ ∈ occupiedRealCells S a b := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨Int.floor_mono (hS hx).1,Int.floor_mono (hS hx).2⟩,x,hx,rfl⟩

/-- Counting occupied cells reuses the audited parity-bin selection. -/
theorem occupiedRealCells_card {S : Set ℝ} {a b B : ℝ}
    (hcard : ∀ W : Finset ℝ, (∀ x ∈ W, x ∈ S) → MathCollab.Density.oneSeparated W → (W.card:ℝ) ≤ B) :
    ((occupiedRealCells S a b).card:ℝ) ≤ 2*B := by
  classical
  let K := occupiedRealCells S a b
  have hex : ∀ k : ℤ, ∃ x : ℝ, k ∈ K → x ∈ S ∧ ⌊x⌋ = k := by
    intro k
    by_cases hk : k ∈ K
    · obtain ⟨x,hx,he⟩ := (Finset.mem_filter.mp hk).2
      exact ⟨x,fun _ => ⟨hx,he⟩⟩
    · exact ⟨0,fun h => (hk h).elim⟩
  choose f hf using hex
  obtain ⟨J,hJK,hcount,hpar⟩ := MathCollab.Density.occupied_bins_parity K
  have hfJ : ∀ k ∈ J, f k ∈ S ∧ ⌊f k⌋ = k := fun k hk => hf k (hJK hk)
  have hinj : Set.InjOn f (J : Set ℤ) := by
    intro k hk l hl he
    rw [← (hfJ k hk).2,← (hfJ l hl).2,he]
  have hb := hcard (J.image f) (by
    intro x hx
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    exact (hfJ k hk).1) (by
    intro x hx y hy hxy
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hy
    apply MathCollab.Density.same_parity_bins_separated
    · rw [(hfJ k hk).2,(hfJ l hl).2]
      intro he
      exact hxy (congrArg f he)
    · rw [(hfJ k hk).2,(hfJ l hl).2]
      exact hpar k hk l hl)
  rw [Finset.card_image_of_injOn hinj] at hb
  have hc : (K.card:ℝ) ≤ 2*(J.card:ℝ) := by exact_mod_cast hcount
  linarith

/-- The actual finite set deleted near occupied cells. -/
def quarticDeleted (W : Finset ℝ) (K : Finset ℤ) (R : ℝ) : Finset ℝ :=
  K.biUnion (fun k => W.filter (fun w => |w-(k:ℝ)| ≤ R+1))

theorem quarticDeleted_subset (W : Finset ℝ) (K : Finset ℤ) (R : ℝ) :
    quarticDeleted W K R ⊆ W := by
  intro w hw
  obtain ⟨k,_,hw⟩ := Finset.mem_biUnion.mp hw
  exact (Finset.mem_filter.mp hw).1

/-- Each occupied cell removes at most 2R+3 separated points. -/
theorem quarticDeleted_card {W : Finset ℝ} (hsep : MathCollab.Density.oneSeparated W)
    (K : Finset ℤ) {R : ℝ} (hR : 0 ≤ R) :
    ((quarticDeleted W K R).card:ℝ) ≤ (2*R+3)*K.card := by
  classical
  have hlocal (k : ℤ) : ((W.filter (fun w => |w-(k:ℝ)| ≤ R+1)).card:ℝ) ≤ 2*R+3 := by
    let V := W.filter (fun w => |w-(k:ℝ)| ≤ R+1)
    have hv : MathCollab.Density.oneSeparated V := MathCollab.Density.oneSeparated_subset hsep (Finset.filter_subset _ _)
    have hd := MathCollab.Density.intervalSpan_le_of_forall (by positivity : 0 ≤ 2*(R+1)) (U := V) (by
      intro t ht u hu
      have ht' := (Finset.mem_filter.mp ht).2
      have hu' := (Finset.mem_filter.mp hu).2
      have hh := abs_sub_le t (k:ℝ) u
      rw [abs_sub_comm (k:ℝ) u] at hh
      linarith)
    have hc := MathCollab.Density.separated_card_le_localDiameter hv
    unfold MathCollab.Density.localDiameter at hc
    linarith
  have hh : ((quarticDeleted W K R).card:ℝ) ≤
      ∑ k ∈ K, ((W.filter (fun w => |w-(k:ℝ)| ≤ R+1)).card:ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := K) (t := fun k => W.filter (fun w => |w-(k:ℝ)| ≤ R+1)))
  exact hh.trans ((Finset.sum_le_sum (fun k _ => hlocal k)).trans_eq (by simp only [Finset.sum_const, nsmul_eq_mul]; ring))

/-- Outside deleted cells, the entire R-neighborhood is below the truncation
threshold and inside the exact time-cutoff plateau. -/
theorem quartic_good_neighborhood {N T R U w t : ℝ} (hT : 0 < T)
    (hRT : R ≤ T) (hw : w ∈ Icc (0:ℝ) T) (a : ℕ → ℂ) (W : Finset ℝ)
    (hwW : w ∈ W)
    (hgood : w ∉ quarticDeleted W (occupiedRealCells
      ({x | U < ‖boundedPolynomial N a x‖} ∩ Icc (-T) (2*T)) (-T) (2*T)) R)
    (ht : |t-w| ≤ R) :
    ‖boundedPolynomial N a t‖ ≤ U ∧ fixedTimeCutoff (t/T)=1 := by
  have htI : t ∈ Icc (-T) (2*T) := by
    have ha := abs_le.mp ht
    constructor <;> linarith [hw.1,hw.2,ha.1,ha.2]
  constructor
  · by_contra hh
    have hhigh : t ∈ {x | U < ‖boundedPolynomial N a x‖} ∩ Icc (-T) (2*T) := ⟨lt_of_not_ge hh,htI⟩
    have hk := occupiedRealCells_mem inter_subset_right hhigh
    apply hgood
    apply Finset.mem_biUnion.mpr
    refine ⟨⌊t⌋,hk,Finset.mem_filter.mpr ⟨hwW,?_⟩⟩
    have hlo := Int.floor_le t
    have hhi := Int.lt_floor_add_one t
    have hnear : |t-(⌊t⌋:ℝ)| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    have ha := abs_sub_le w t (⌊t⌋:ℝ)
    rw [abs_sub_comm w t] at ha
    linarith
  · apply fixedTimeCutoff_one
    constructor
    · apply (le_div_iff₀ hT).mpr
      linarith [htI.1]
    · apply (div_le_iff₀ hT).mpr
      linarith [htI.2]

end GuthMaynard.Improvement
#print axioms GuthMaynard.Improvement.occupiedRealCells_mem
#print axioms GuthMaynard.Improvement.occupiedRealCells_card
#print axioms GuthMaynard.Improvement.quarticDeleted_subset
#print axioms GuthMaynard.Improvement.quarticDeleted_card
#print axioms GuthMaynard.Improvement.quartic_good_neighborhood
