import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeInactiveAndFarTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeBudget

/-!
# Quantitative finite inactive packet budget

The finite inactive family is decomposed into left-nonstationary modes,
right-nonstationary modes, and the unique zero-frequency transition mode.
The first two classes consume the explicit first-derivative packet estimates;
the transition class consumes the unconditional zero-mode estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhaseQuantitativeLeftInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

def Complex.logarithmicPhaseQuantitativeRightInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

def Complex.logarithmicPhaseQuantitativeTransitionBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

def Complex.logarithmicPhaseQuantitativeLeftInactiveExplicitBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
    (2 / 3 +
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
          (b : ℝ))⁻¹ +
      ((b : ℝ) - (a : ℝ)) •
        ((‖t‖ / (a : ℝ) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
              (b : ℝ)) ^ 2))

def Complex.logarithmicPhaseQuantitativeRightInactiveExplicitBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
    (2 / 3 +
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
          (b : ℝ))⁻¹ +
      ((b : ℝ) - (a : ℝ)) •
        ((‖t‖ / (a : ℝ) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
              (b : ℝ)) ^ 2))

def Complex.logarithmicPhaseQuantitativeInactiveExplicitBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeLeftInactiveExplicitBudget t a b +
    Complex.logarithmicPhaseQuantitativeRightInactiveExplicitBudget t a b +
      Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b

theorem Complex.logarithmicPhaseQuantitativeLeftInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseQuantitativeLeftInactiveBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeLeftInactiveBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeRightInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseQuantitativeRightInactiveBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeRightInactiveBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeTransitionBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseQuantitativeTransitionBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeTransitionBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_eq_three_parts
    (t : ℝ) (a b : ℤ)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b =
      Complex.logarithmicPhaseQuantitativeLeftInactiveBudget t a b +
        Complex.logarithmicPhaseQuantitativeRightInactiveBudget t a b +
          Complex.logarithmicPhaseQuantitativeTransitionBudget t a b := by
  let left := Complex.logarithmicPhasePoissonLeftInactiveModes t a b
  let right := Complex.logarithmicPhasePoissonRightInactiveModes t a b
  let transition := Complex.logarithmicPhasePoissonTransitionModes t a b
  let inactive := Complex.logarithmicPhasePoissonInRangeInactiveModes t a b
  let packetNorm : ℤ → ℝ := fun m =>
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖
  have hleftRight : Disjoint left right :=
    Complex.logarithmicPhasePoissonLeftRightInactive_disjoint t a b hab
  have hcoreTransition : Disjoint (left ∪ right) transition :=
    Complex.logarithmicPhasePoissonLeftRightInactive_disjoint_transition t a b
  have hpartition : (left ∪ right) ∪ transition = inactive :=
    Complex.logarithmicPhasePoissonLeftRightTransition_union_eq_inRangeInactive
      t a b
  have hleftRightSum :
      (∑ m ∈ left ∪ right, packetNorm m) =
        (∑ m ∈ left, packetNorm m) +
          ∑ m ∈ right, packetNorm m :=
    Finset.sum_union hleftRight
  have hcoreTransitionSum :
      (∑ m ∈ (left ∪ right) ∪ transition, packetNorm m) =
        (∑ m ∈ left ∪ right, packetNorm m) +
          ∑ m ∈ transition, packetNorm m :=
    Finset.sum_union hcoreTransition
  unfold Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget
  unfold Complex.logarithmicPhaseQuantitativeLeftInactiveBudget
  unfold Complex.logarithmicPhaseQuantitativeRightInactiveBudget
  unfold Complex.logarithmicPhaseQuantitativeTransitionBudget
  change
    (∑ m ∈ inactive, packetNorm m) =
      (∑ m ∈ left, packetNorm m) +
        (∑ m ∈ right, packetNorm m) +
          ∑ m ∈ transition, packetNorm m
  exact Eq.trans
    (congrArg
      (fun modes : Finset ℤ => ∑ m ∈ modes, packetNorm m)
      hpartition.symm)
    (Eq.trans hcoreTransitionSum
      (congrArg
        (fun core : ℝ => core + ∑ m ∈ transition, packetNorm m)
        hleftRightSum))

theorem Complex.logarithmicPhaseQuantitativeTransitionBudget_eq_zeroPacket
    (t : ℝ) {a b : ℤ}
    (ha : 1 ≤ a) :
    Complex.logarithmicPhaseQuantitativeTransitionBudget t a b =
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b 0‖ := by
  have hmodes :=
    Complex.logarithmicPhasePoissonTransitionModes_eq_singleton_zero
      t (a := a) (b := b) ha
  unfold Complex.logarithmicPhaseQuantitativeTransitionBudget
  exact Eq.trans
    (congrArg
      (fun modes : Finset ℤ =>
        ∑ m ∈ modes,
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)
      hmodes)
    Finset.sum_singleton

theorem Complex.logarithmicPhaseQuantitativeTransitionBudget_le_zeroModeBudget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeTransitionBudget t a b ≤
      Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b := by
  have hidentity :=
    Complex.logarithmicPhaseQuantitativeTransitionBudget_eq_zeroPacket
      t (a := a) (b := b) ha
  have hzero :=
    Complex.norm_logarithmicPhaseQuantitativeZeroPacket_le_budget
      t ht htNonneg a b ha hab
  exact Eq.subst
    (motive := fun transitionBudget : ℝ =>
      transitionBudget ≤
        Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b)
    hidentity.symm
    hzero

theorem Complex.logarithmicPhaseQuantitativeLeftInactiveBudget_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeLeftInactiveBudget t a b ≤
      Complex.logarithmicPhaseQuantitativeLeftInactiveExplicitBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeLeftInactiveBudget
  unfold Complex.logarithmicPhaseQuantitativeLeftInactiveExplicitBudget
  exact Finset.sum_le_sum
    (fun m hm =>
      have hmem :=
        (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
          t a b m).mp hm
      Complex.norm_logarithmicPhaseQuantitativePacket_le_leftInactive_explicit
        t ht htNonneg a b m ha hab hmem.2.1 hmem.2.2)

theorem Complex.logarithmicPhaseQuantitativeRightInactiveBudget_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeRightInactiveBudget t a b ≤
      Complex.logarithmicPhaseQuantitativeRightInactiveExplicitBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeRightInactiveBudget
  unfold Complex.logarithmicPhaseQuantitativeRightInactiveExplicitBudget
  exact Finset.sum_le_sum
    (fun m hm =>
      have hmem :=
        (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
          t a b m).mp hm
      Complex.norm_logarithmicPhaseQuantitativePacket_le_rightInactive_explicit
        t ht htNonneg a b m ha hab hmem.2.1 hmem.2.2)

theorem Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
      Complex.logarithmicPhaseQuantitativeInactiveExplicitBudget t a b := by
  have hdecomposition :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_eq_three_parts
      t a b hab
  have hleft :=
    Complex.logarithmicPhaseQuantitativeLeftInactiveBudget_le_explicit
      t ht htNonneg a b ha hab
  have hright :=
    Complex.logarithmicPhaseQuantitativeRightInactiveBudget_le_explicit
      t ht htNonneg a b ha hab
  have htransition :=
    Complex.logarithmicPhaseQuantitativeTransitionBudget_le_zeroModeBudget
      t ht htNonneg a b ha hab
  unfold Complex.logarithmicPhaseQuantitativeInactiveExplicitBudget
  exact le_trans
    (le_of_eq hdecomposition)
    (add_le_add (add_le_add hleft hright) htransition)

theorem Complex.norm_logarithmicPhaseQuantitativeLeftInactive_tsum_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeLeftInactiveExplicitBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeLeftInactiveExplicitBudget
  exact
    Complex.norm_logarithmicPhaseQuantitative_leftInactivePacket_tsum_le_explicit_sum
      t ht htNonneg a b ha hab
      (Complex.logarithmicPhasePoissonLeftInactiveModes t a b)
      (fun m hm =>
        have hmem :=
          (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
            t a b m).mp hm
        ⟨hmem.2.1, hmem.2.2⟩)

theorem Complex.norm_logarithmicPhaseQuantitativeRightInactive_tsum_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeRightInactiveExplicitBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeRightInactiveExplicitBudget
  exact
    Complex.norm_logarithmicPhaseQuantitative_rightInactivePacket_tsum_le_explicit_sum
      t ht htNonneg a b ha hab
      (Complex.logarithmicPhasePoissonRightInactiveModes t a b)
      (fun m hm =>
        have hmem :=
          (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
            t a b m).mp hm
        ⟨hmem.2.1, hmem.2.2⟩)

theorem Complex.logarithmicPhasePoissonLeftInactive_center_lt_supportLeft
    (t : ℝ) (a b m : ℤ)
    (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    Complex.logarithmicPhaseFourierStationaryPoint t m <
      Real.integerBlockCutoffSupportLeftEndpoint a := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp hm
  have hinactive := Finset.mem_sdiff.mp hmem.1
  have hmRange := hinactive.1
  have hmNotActive := hinactive.2
  have hmNegative := hmem.2.1
  have hcenterLtA := hmem.2.2
  have hmarginNonneg : (0 : ℝ) ≤ 2 / 3 :=
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hcenterUpper :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        (b : ℝ) + 2 / 3 :=
    le_trans (le_trans (le_of_lt hcenterLtA) habReal)
      (le_add_of_nonneg_right hmarginNonneg)
  match lt_or_ge
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Real.integerBlockCutoffSupportLeftEndpoint a) with
  | Or.inl hleft => exact hleft
  | Or.inr hnotLeft =>
      have hcenterMembership :
          Complex.logarithmicPhaseFourierStationaryPoint t m ∈
            Set.Icc
              (Real.integerBlockCutoffSupportLeftEndpoint a)
              ((b : ℝ) + 2 / 3) :=
        ⟨hnotLeft, hcenterUpper⟩
      have hactive :
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b :=
        (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mpr
          ⟨hmRange, hmNegative, hcenterMembership⟩
      exact False.elim (hmNotActive hactive)

theorem Complex.logarithmicPhasePoissonRightInactive_supportRight_lt_center
    (t : ℝ) (a b m : ℤ)
    (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    (b : ℝ) + 2 / 3 <
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hm
  have hinactive := Finset.mem_sdiff.mp hmem.1
  have hmRange := hinactive.1
  have hmNotActive := hinactive.2
  have hmNegative := hmem.2.1
  have hbLtCenter := hmem.2.2
  have hmarginNonneg : (0 : ℝ) ≤ 2 / 3 :=
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
  have hsupportLeftLeA :
      Real.integerBlockCutoffSupportLeftEndpoint a ≤ (a : ℝ) := by
    unfold Real.integerBlockCutoffSupportLeftEndpoint
    exact sub_le_self _ hmarginNonneg
  have hsupportLeftLeCenter :
      Real.integerBlockCutoffSupportLeftEndpoint a ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m :=
    le_trans hsupportLeftLeA
      (le_trans (Int.cast_le.mpr hab) (le_of_lt hbLtCenter))
  match lt_or_ge
      ((b : ℝ) + 2 / 3)
      (Complex.logarithmicPhaseFourierStationaryPoint t m) with
  | Or.inl hright => exact hright
  | Or.inr hnotRight =>
      have hcenterMembership :
          Complex.logarithmicPhaseFourierStationaryPoint t m ∈
            Set.Icc
              (Real.integerBlockCutoffSupportLeftEndpoint a)
              ((b : ℝ) + 2 / 3) :=
        ⟨hsupportLeftLeCenter, hnotRight⟩
      have hactive :
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b :=
        (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mpr
          ⟨hmRange, hmNegative, hcenterMembership⟩
      exact False.elim (hmNotActive hactive)

theorem Complex.logarithmicPhasePoissonLeftInactive_twoThirds_lt_gap
    (t : ℝ) (a b m : ℤ)
    (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    (2 : ℝ) / 3 <
      (a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hcenter :=
    Complex.logarithmicPhasePoissonLeftInactive_center_lt_supportLeft
      t a b m hab hm
  unfold Real.integerBlockCutoffSupportLeftEndpoint at hcenter
  have htransport := sub_lt_sub_left hcenter (a : ℝ)
  have hnormalize :
      (a : ℝ) - ((a : ℝ) - 2 / 3) = (2 : ℝ) / 3 := by
    calc
      (a : ℝ) - ((a : ℝ) - 2 / 3) =
          ((a : ℝ) - (a : ℝ)) + 2 / 3 :=
        sub_sub (a : ℝ) (a : ℝ) (2 / 3)
      _ = 0 + 2 / 3 :=
        congrArg (fun value : ℝ => value + 2 / 3) (sub_self (a : ℝ))
      _ = 2 / 3 := zero_add _
  exact Eq.subst
    (motive := fun leftGap : ℝ =>
      leftGap < (a : ℝ) -
        Complex.logarithmicPhaseFourierStationaryPoint t m)
    hnormalize
    htransport

theorem Complex.logarithmicPhasePoissonRightInactive_twoThirds_lt_gap
    (t : ℝ) (a b m : ℤ)
    (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    (2 : ℝ) / 3 <
      Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ) := by
  have hcenter :=
    Complex.logarithmicPhasePoissonRightInactive_supportRight_lt_center
      t a b m hab hm
  have htransport := sub_lt_sub_right hcenter (b : ℝ)
  have hnormalize :
      ((b : ℝ) + 2 / 3) - (b : ℝ) = (2 : ℝ) / 3 := by
    calc
      ((b : ℝ) + 2 / 3) - (b : ℝ) =
          ((b : ℝ) - (b : ℝ)) + 2 / 3 :=
        add_sub_right_comm (b : ℝ) (2 / 3) (b : ℝ)
      _ = 0 + 2 / 3 :=
        congrArg (fun value : ℝ => value + 2 / 3) (sub_self (b : ℝ))
      _ = 2 / 3 := zero_add _
  exact Eq.subst
    (motive := fun leftGap : ℝ =>
      leftGap <
        Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ))
    hnormalize
    htransport

theorem Complex.logarithmicPhasePoissonLeftInactive_gap_pos
    (t : ℝ) (a b m : ℤ)
    (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    0 < (a : ℝ) -
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hthirds :=
    Complex.logarithmicPhasePoissonLeftInactive_twoThirds_lt_gap
      t a b m hab hm
  have htwoThirdsPos : (0 : ℝ) < 2 / 3 :=
    div_pos (Nat.cast_pos.mpr (Nat.succ_pos 1))
      (Nat.cast_pos.mpr (Nat.succ_pos 2))
  exact lt_trans htwoThirdsPos hthirds

theorem Complex.logarithmicPhasePoissonRightInactive_gap_pos
    (t : ℝ) (a b m : ℤ)
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    0 < Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ) := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hm
  exact sub_pos.mpr hmem.2.2

end
end LFunctions
end Boundary
