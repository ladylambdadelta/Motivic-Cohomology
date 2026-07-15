import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessBudget

/-!
# Quantitative finite inactive packet decomposition

The in-range inactive family is the disjoint union of left-inactive modes,
right-inactive modes, and the singleton zero mode.  This owner reproduces the
decomposition for the quantitative Poisson packet and exposes the sharp
zero-frequency logarithmic estimate separately from the two nonzero finite
families.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

def Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

def Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

theorem Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget_eq_zeroPacketNorm
    (t : ℝ) {a b : ℤ} (ha : 1 ≤ a) :
    Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget t a b =
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b 0‖ := by
  have hmodes :=
    Complex.logarithmicPhasePoissonTransitionModes_eq_singleton_zero
      t (a := a) (b := b) ha
  unfold Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget
  calc
    (∑ m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b,
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖) =
        ∑ m ∈ ({0} : Finset ℤ),
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ := by
      exact congrArg
        (fun modes : Finset ℤ =>
          ∑ m ∈ modes,
            ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)
        hmodes
    _ = ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b 0‖ :=
      Finset.sum_singleton
        (fun m : ℤ =>
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)
        0

theorem Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget_le_zeroModeBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    {a b : ℤ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget t a b ≤
      Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b := by
  have htransition :=
    Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget_eq_zeroPacketNorm
      t (a := a) (b := b) ha
  have hzero :=
    Complex.norm_logarithmicPhaseQuantitativeZeroPacket_le
      t ht ht_nonneg a b ha hab
  unfold Complex.logarithmicPhaseQuantitativeZeroModeBudget
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤ 2 / 3 + 2 * ((b : ℝ) / ‖t‖) +
        ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹)
    htransition.symm hzero

theorem Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_eq_left_add_right_add_transition
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b =
      Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b +
        Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b +
          Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget t a b := by
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
        (∑ m ∈ left, packetNorm m) + ∑ m ∈ right, packetNorm m :=
    Finset.sum_union hleftRight
  have hcoreTransitionSum :
      (∑ m ∈ (left ∪ right) ∪ transition, packetNorm m) =
        (∑ m ∈ left ∪ right, packetNorm m) +
          ∑ m ∈ transition, packetNorm m :=
    Finset.sum_union hcoreTransition
  unfold Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget
  unfold Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
  unfold Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
  unfold Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget
  exact Eq.trans
    (congrArg (fun modes : Finset ℤ => ∑ m ∈ modes, packetNorm m)
      hpartition.symm)
    (Eq.trans hcoreTransitionSum
      (congrArg
        (fun value : ℝ => value + ∑ m ∈ transition, packetNorm m)
        hleftRightSum))

theorem Complex.norm_logarithmicPhaseQuantitativeLeftInactive_tsum_le_budget
    (t : ℝ) (a b : ℤ) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b := by
  have hfinite :=
    (Complex.logarithmicPhasePoissonLeftInactiveModes t a b).tsum_subtype
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  unfold Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        ∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)
    hfinite.symm
    (norm_sum_le _ _)

theorem Complex.norm_logarithmicPhaseQuantitativeRightInactive_tsum_le_budget
    (t : ℝ) (a b : ℤ) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b := by
  have hfinite :=
    (Complex.logarithmicPhasePoissonRightInactiveModes t a b).tsum_subtype
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  unfold Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        ∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)
    hfinite.symm
    (norm_sum_le _ _)

theorem Complex.norm_logarithmicPhaseQuantitativeTransition_tsum_le_budget
    (t : ℝ) (a b : ℤ) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget t a b := by
  have hfinite :=
    (Complex.logarithmicPhasePoissonTransitionModes t a b).tsum_subtype
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  unfold Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        ∑ m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b,
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)
    hfinite.symm
    (norm_sum_le _ _)

theorem Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_left_add_right_add_zero
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
      Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b +
        Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b +
          Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b := by
  have hpartition :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_eq_left_add_right_add_transition
      t a b hab
  have hzero :=
    Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget_le_zeroModeBudget
      t ht ht_nonneg ha hab
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤
        Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b +
          Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b +
            Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b)
    hpartition.symm
    (add_le_add_left hzero
      (Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b +
        Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b))

end

end LFunctions
end Boundary
