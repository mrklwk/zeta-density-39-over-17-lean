module
public import GenericPacketCounting
public import MathCollab.Density.Stronger.Peaks.ClusterCount

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.CriticalPeak
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks

/-- Analytic interface for a general pair; the native pair producer must supply it. -/
def PairLocalMeanPacket (k l : ℝ) : Prop :=
  ∀ δ κ ν : ℝ, 0 < δ → 0 < κ → 0 < ν →
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G L : ℝ) (W : Finset ℝ), H₀ ≤ H → 0 < G → 0 < L →
        separatedAt G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) →
        (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
          D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l))

def LocalMeanCount (a g b : ℝ) : Prop :=
  ∀ δ κ ν : ℝ, 0 < δ → 0 < κ → 0 < ν →
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G Y : ℝ) (W : Finset ℝ), H₀ ≤ H → 0 < G → 0 < Y →
        separatedAt G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t)) →
        (W.card:ℝ) ≤ D*H^ν*(H/(G*Y^2)+H^a/(G^g*Y^b))

theorem localMeanCount_of_pair_packet {k l : ℝ} (hk : 0 < k)
    (hPacket : PairLocalMeanPacket k l) :
    LocalMeanCount (1+l/k) ((2*l-1)/k) (2+2/k) := by
  intro δ κ ν hδ hκ hν
  have hq : 0 < 1+1/k := by positivity
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    hPacket δ κ (ν/(1+1/k)) hδ hκ (div_pos hν hq)
  refine ⟨C,hC,2*D+2*4^(1/k)*D^(1+1/k),by positivity,B,hB,?_⟩
  intro H G Y W hH hG hY hsep hrange hlarge
  have hH1 : 1 ≤ H := by linarith [hB.trans hH]
  have hH0 : 0 < H := by linarith
  have hA : 0 < D*H^(ν/(1+1/k)) := by positivity
  have hL := absorptionLength_pos (k := k) (l := l) hA hH0 hG hY
  have hpacket : ∀ U : Finset ℝ, U ⊆ W → ∀ A : ℝ,
      (∀ t ∈ U, A ≤ t ∧ t ≤ A+absorptionLength k l (D*H^(ν/(1+1/k))) H G Y) →
        (∑ t ∈ U, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
          (D*H^(ν/(1+1/k)))*((U.card:ℝ)*H/G+(U.card:ℝ)^2*
            ((absorptionLength k l (D*H^(ν/(1+1/k))) H G Y)^k*H^(l-k)*G^(1+k-2*l))) := by
    intro U hsub A hlocal
    have hsepU : separatedAt G U := by
      intro x hx y hy hxy
      exact hsep x (hsub hx) y (hsub hy) hxy
    have hdiam : ∀ t ∈ U, ∀ u ∈ U,
        |u-t| ≤ absorptionLength k l (D*H^(ν/(1+1/k))) H G Y := by
      intro t ht u hu
      rw [abs_le]
      constructor <;> linarith [(hlocal t ht).1,(hlocal t ht).2,
        (hlocal u hu).1,(hlocal u hu).2]
    have hs := hsource H G (absorptionLength k l (D*H^(ν/(1+1/k))) H G Y)
      U hH hG hL hsepU (fun t ht => hrange t (hsub ht)) hdiam
    convert hs using 1
    ring
  have hc := card_le_two_powers hk hA hH0 hG hY
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hlarge hpacket
  exact hc.trans (count_exponent_budget hk hD.le hH1 hG hY hν.le)
end Montgomery.CriticalPeak
