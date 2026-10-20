module

public import CountAdapter
public import FinalDensitySurface.Pieces

/-!
# Proved solution surface

No import of Challenge. The count definitions are supplied by CountCore with
the same fixed bodies as Challenge. CountAdapter proves their exact equality
to the existing natural-valued count; no analytic/finiteness hypothesis is
assumed. Every advertised proof is an exact count transfer from the frozen
statement surface, preserving endpoints and the constant's quantifier order.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal
public section
namespace LewkoDensityPalomar

theorem provider_P1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P1 hlo hhi hε)

theorem provider_P2 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ < (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P2 hlo hhi hε)

theorem provider_P3 {σ ε : ℝ} (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P3 hlo hhi hε)

theorem provider_P4 {σ ε : ℝ} (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P4 hlo hhi hε)

theorem provider_P5 {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ < (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P5 hlo hhi hε)

theorem provider_P6 {σ ε : ℝ} (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P6 hlo hhi hε)

theorem provider_P7 {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ < (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P7 hlo hhi hε)

theorem provider_P8 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (1867/2347 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P8 hlo hhi hε)

theorem provider_P9 {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P9 hlo hhi hε)

theorem provider_P10 {σ ε : ℝ} (hlo : (7/10 : ℝ) < σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P10 hlo hhi hε)

theorem provider_P11 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P11 hlo hhi hε)

theorem provider_P12 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P12 hlo hhi hε)

theorem provider_P13 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ < (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P13 hlo hhi hε)

theorem provider_P14 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P14 hlo hhi hε)

theorem provider_P15 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((12/(9*σ-1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P15 hlo hhi hε)

theorem provider_P16 {σ ε : ℝ} (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((255/(153*σ+7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P16 hlo hhi hε)

theorem provider_P17 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(11*σ-7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P17 hlo hhi hε)

theorem provider_P18 {σ ε : ℝ} (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P18 hlo hhi hε)

theorem provider_P19 {σ ε : ℝ} (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P19 hlo hhi hε)

theorem provider_P20 {σ ε : ℝ} (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P20 hlo hhi hε)

theorem provider_P21 {σ ε : ℝ} (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P21 hlo hhi hε)

theorem provider_P22 {σ ε : ℝ} (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((566/(606*σ-173))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P22 hlo hhi hε)

theorem provider_P23 {σ ε : ℝ} (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P23 hlo hhi hε)

theorem provider_P24 {σ ε : ℝ} (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P24 hlo hhi hε)

theorem provider_P25 {σ ε : ℝ} (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P25 hlo hhi hε)

theorem provider_P26 {σ ε : ℝ} (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P26 hlo hhi hε)

theorem provider_P27 {σ ε : ℝ} (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P27 hlo hhi hε)

theorem provider_P28 {σ ε : ℝ} (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P28 hlo hhi hε)

theorem provider_P29 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P29 hlo hhi hε)

theorem provider_P30 {σ ε : ℝ} (hlo : (19/22 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P30 hlo hhi hε)

theorem provider_P31 {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P31 hlo hhi hε)

theorem piece_G1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G1 hlo hhi hε)

theorem piece_G2 {σ ε : ℝ} (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G2 hlo hhi hε)

theorem piece_G3 {σ ε : ℝ} (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G3 hlo hhi hε)

theorem piece_G4 {σ ε : ℝ} (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G4 hlo hhi hε)

theorem piece_G5 {σ ε : ℝ} (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G5 hlo hhi hε)

theorem piece_G6 {σ ε : ℝ} (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G6 hlo hhi hε)

theorem piece_G7 {σ ε : ℝ} (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G7 hlo hhi hε)

theorem piece_G8 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (23/29 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G8 hlo hhi hε)

theorem piece_G9 {σ ε : ℝ} (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G9 hlo hhi hε)

theorem piece_G10 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G10 hlo hhi hε)

theorem piece_B1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B1 hlo hhi hε)

theorem piece_B2 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B2 hlo hhi hε)

theorem piece_B3 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (11/15 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B3 hlo hhi hε)

theorem piece_B4 {σ ε : ℝ} (hlo : (11/15 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B4 hlo hhi hε)

theorem piece_B5 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B5 hlo hhi hε)

theorem piece_B6 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B6 hlo hhi hε)

theorem piece_O1 {σ ε : ℝ} (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O1 hlo hhi hε)

theorem piece_O2 {σ ε : ℝ} (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (12/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O2 hlo hhi hε)

theorem piece_O3 {σ ε : ℝ} (hlo : (12/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O3 hlo hhi hε)

theorem piece_O4 {σ ε : ℝ} (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((12/(9*σ-1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O4 hlo hhi hε)

theorem piece_O5 {σ ε : ℝ} (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((255/(153*σ+7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O5 hlo hhi hε)

theorem piece_O6 {σ ε : ℝ} (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O6 hlo hhi hε)

theorem piece_O7 {σ ε : ℝ} (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(11*σ-7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O7 hlo hhi hε)

theorem piece_O8 {σ ε : ℝ} (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O8 hlo hhi hε)

theorem piece_O9 {σ ε : ℝ} (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O9 hlo hhi hε)

theorem piece_O10 {σ ε : ℝ} (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O10 hlo hhi hε)

theorem piece_O11 {σ ε : ℝ} (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O11 hlo hhi hε)

theorem piece_O12 {σ ε : ℝ} (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((566/(606*σ-173))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O12 hlo hhi hε)

theorem piece_O13 {σ ε : ℝ} (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O13 hlo hhi hε)

theorem piece_O14 {σ ε : ℝ} (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O14 hlo hhi hε)

theorem piece_O15 {σ ε : ℝ} (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O15 hlo hhi hε)

theorem piece_O16 {σ ε : ℝ} (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O16 hlo hhi hε)

theorem piece_O17 {σ ε : ℝ} (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O17 hlo hhi hε)

theorem piece_O18 {σ ε : ℝ} (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O18 hlo hhi hε)

theorem piece_O19 {σ ε : ℝ} (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (24139/27578 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O19 hlo hhi hε)

theorem piece_O20 {σ ε : ℝ} (hlo : (24139/27578 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O20 hlo hhi hε)

theorem piece_O21 {σ ε : ℝ} (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/19 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O21 hlo hhi hε)

theorem piece_O22 {σ ε : ℝ} (hlo : (17/19 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O22 hlo hhi hε)

theorem global39over17 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (1/2 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((39/17 : ℝ)*(1-σ)) + ε)) := by
  obtain ⟨C, hC, hb⟩ := FinalDensitySurface.global39over17 hε
  refine ⟨C, hC, ?_⟩
  intro σ T hlo hhi hT
  obtain ⟨F, hF⟩ := exact_zero_set_exists σ T
  rw [zeroCount_eq_finset σ T F hF, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hb σ T hlo hhi hT F hF)

theorem uniform_P29 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/8 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  obtain ⟨C, hC, hb⟩ := FinalDensitySurface.uniform_P29 hε
  refine ⟨C, hC, ?_⟩
  intro σ T hlo hhi hT
  obtain ⟨F, hF⟩ := exact_zero_set_exists σ T
  rw [zeroCount_eq_finset σ T F hF, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hb σ T hlo hhi hT F hF)

theorem uniform_P30 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22 : ℝ) ≤ σ →
      σ ≤ (23/26 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  obtain ⟨C, hC, hb⟩ := FinalDensitySurface.uniform_P30 hε
  refine ⟨C, hC, ?_⟩
  intro σ T hlo hhi hT
  obtain ⟨F, hF⟩ := exact_zero_set_exists σ T
  rw [zeroCount_eq_finset σ T F hF, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hb σ T hlo hhi hT F hF)

theorem uniform_P31 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  obtain ⟨C, hC, hb⟩ := FinalDensitySurface.uniform_P31 hε
  refine ⟨C, hC, ?_⟩
  intro σ T hlo hhi hT
  obtain ⟨F, hF⟩ := exact_zero_set_exists σ T
  rw [zeroCount_eq_finset σ T F hF, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hb σ T hlo hhi hT F hF)

end LewkoDensityPalomar
