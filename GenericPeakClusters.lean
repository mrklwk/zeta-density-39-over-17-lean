module
/- Generalized from the attributed McColm peak-cluster proof in the verified baseline.
The actual native point-mean theorem is supplied here; the general-pair local count
remains an internal interface to be discharged by the analytic pair producer. -/
public import GenericMeanCounting
public import MathCollab.Density.Stronger.PointMean.PeaksInput

@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.CriticalPeak
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
theorem exists_pointCluster_superlevel_count
    {a g b : ℝ} (hCount : LocalMeanCount a g b)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ) (m : ℕ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) → 0 < m →
        ((pointClusterSuperlevel H G W m).card:ℝ) ≤
          2*D*H^ν*
            (H/(G*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^2) +
              H^a/(G^g*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^b)) := by
  obtain ⟨P,hP,hentry⟩ := (exists_pointCluster_superlevel_entry PointMean.pointMeanInput_native)
  obtain ⟨C,hC,D,hD,H₀,hH₀,hcount⟩ :=
    hCount δ κ ν hδ hκ hν
  refine ⟨P,C,D,H₀,hP,hC,hD,hH₀,?_⟩
  intro H G V W m hH hG hGH hV hfit hwidth hVsize herr hsep hrange hlarge hm
  let A : ℝ := V^2/(16*P*Real.log (3*H))
  let Y : ℝ := (m:ℝ)*A
  let S : Finset ℕ := pointClusterSuperlevel H G W m
  have hHlarge : 20 ≤ H := by linarith [hH₀.trans hH]
  have hL : 0 < Real.log (3*H) := Real.log_pos (by linarith)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hcolor : ∀ e : ℕ,
      ((S.filter (fun n => n%2 = e)).card:ℝ) ≤
        D*H^ν*(H/(G*Y^2)+H^a/(G^g*Y^b)) := by
    intro e
    let U := S.filter (fun n => n%2 = e)
    have hbase : ∀ n ∈ U, n ∈ pointClusterBins H G W := by
      intro n hn
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hcentersSep := pointClusterCenters_separated (H := H) hG U e
      (fun n hn => (Finset.mem_filter.mp hn).2)
    have hcentersRange : ∀ t ∈ pointClusterCenters H G U,
        H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G := by
      intro t ht
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
      have hc := pointClusterCenter_range hG hrange (hbase n hn)
      exact ⟨hc.1,hc.2,hwidth _ hc.1 hc.2⟩
    have hcentersLarge : ∀ t ∈ pointClusterCenters H G U,
        Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t) := by
      intro t ht
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
      have hc := pointClusterCenter_range hG hrange (hbase n hn)
      have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
      have hocc : m ≤ (pointCluster H G W n).card := (Finset.mem_filter.mp hnS).2
      have hlog : Real.log (pointClusterCenter H G n) ≤ Real.log (3*H) :=
        Real.log_le_log (by linarith [hc.1]) (by linarith [hc.2])
      have herror : C*G*Real.log (pointClusterCenter H G n) ≤ A :=
        (mul_le_mul_of_nonneg_left hlog (by positivity)).trans herr
      apply (atkinsonLocalMeanExcess_threshold_iff hY).mpr
      exact hentry H G V (C*G*Real.log (pointClusterCenter H G n))
        W n m hHlarge hG hGH hV hfit hsep hrange hlarge
        (hbase n hn) hm hocc hVsize herror
    have hb := hcount H G Y (pointClusterCenters H G U)
      hH hG hY hcentersSep hcentersRange hcentersLarge
    simpa only [pointClusterCenters_card hG, U] using hb
  have hcards : (S.card:ℝ) = ((S.filter (fun n => n%2 = 0)).card:ℝ) +
      ((S.filter (fun n => n%2 = 1)).card:ℝ) := by
    exact_mod_cast card_eq_sum_parity_cards S
  change (S.card:ℝ) ≤ 2*D*H^ν*(H/(G*Y^2)+H^a/(G^g*Y^b))
  rw [hcards]
  have h0 := hcolor 0
  have h1 := hcolor 1
  linarith

theorem occupancy_inverse_power_budget {a g b H G A m : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hA : 0 < A) (hm : 1 ≤ m) (hb : 2 ≤ b) :
    H/(G*(m*A)^2)+H^a/(G^g*(m*A)^b) ≤
      (H/(G*A^2)+H^a/(G^g*A^b))/m^2 := by
  have hm0 : 0 < m := by linarith
  have hp : m^2 ≤ m^b := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hm hb
  rw [mul_pow, Real.mul_rpow hm0.le hA.le]
  calc
    _ ≤ H/(G*(m^2*A^2))+H^a/(G^g*(m^2*A^b)) := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hH a).le (by positivity)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
    _ = _ := by field_simp

theorem exists_pointValue_card_le_with_width
    {a g b : ℝ} (hb : 2 ≤ b) (hCount : LocalMeanCount a g b)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H/(G*(V^2/(16*P*Real.log (3*H)))^2) +
            H^a/(G^g*(V^2/(16*P*Real.log (3*H)))^b)) := by
  obtain ⟨P,C,D,H₀,hP,hC,hD,hH₀,hcount⟩ :=
    (exists_pointCluster_superlevel_count hCount) hδ hκ hν
  refine ⟨P,C,4*D,H₀,hP,hC,by positivity,hH₀,?_⟩
  intro H G V W hH hG hGH hV hfit hwidth hVsize herr hsep hrange hlarge
  let A : ℝ := V^2/(16*P*Real.log (3*H))
  let B : ℝ := 2*D*H^ν*(H/(G*A^2)+H^a/(G^g*A^b))
  have hHpos : 0 < H := by linarith [hH₀.trans hH]
  have hL : 0 < Real.log (3*H) := Real.log_pos (by linarith [hH₀.trans hH])
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsuper : ∀ m : ℕ, 0 < m →
      (((pointClusterBins H G W).filter
        (fun n => m ≤ (pointCluster H G W n).card)).card:ℝ) ≤ B/(m:ℝ)^2 := by
    intro m hm
    have hc := hcount H G V W m hH hG hGH hV hfit hwidth hVsize herr hsep hrange hlarge hm
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hp := occupancy_inverse_power_budget (a := a) (g := g) hHpos hG hA hm1 hb
    calc
      _ ≤ 2*D*H^ν*(H/(G*((m:ℝ)*A)^2)+H^a/(G^g*((m:ℝ)*A)^b)) := hc
      _ ≤ 2*D*H^ν*((H/(G*A^2)+H^a/(G^g*A^b))/(m:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = B/(m:ℝ)^2 := by dsimp only [B]; ring
  have hsum := sum_nat_occupancy_le_of_superlevels
    (pointClusterBins H G W) (fun n => (pointCluster H G W n).card) hB hsuper
  have hpartition : (W.card:ℝ) = ∑ n ∈ pointClusterBins H G W,
      ((pointCluster H G W n).card:ℝ) := by
    exact_mod_cast pointCluster_card_partition H G W
  rw [← hpartition] at hsum
  calc
    (W.card:ℝ) ≤ 2*B := hsum
    _ = (4*D)*H^ν*(H/(G*A^2)+H^a/(G^g*A^b)) := by dsimp only [B]; ring



end Montgomery.CriticalPeak
