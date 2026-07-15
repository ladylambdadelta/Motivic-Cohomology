import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessOutsideEndpointPackets

/-!
# Balanced clipped stationary endpoint packets

For an endpoint mode whose center remains inside `[a,b]`, clip the balanced
window to the principal block.  The clipped central integral has norm at most
`2r`.  A tail on a clipped side is zero; an unclipped side is controlled by
the exact monotone reciprocal-gap estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhaseBProcessClippedWindowLeft
    (t : ℝ) (a m : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
    a (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)

def Complex.logarithmicPhaseBProcessClippedWindowRight
    (t : ℝ) (b m : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeEndpointWindowRight
    b (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)

def Complex.logarithmicPhaseBProcessClippedLeftTailBudget
    (t : ℝ) (a m : ℤ) : ℝ :=
  if (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m then
    Complex.logarithmicPhaseBProcessLeftTailBudget t m
  else 0

def Complex.logarithmicPhaseBProcessClippedRightTailBudget
    (t : ℝ) (b m : ℤ) : ℝ :=
  if Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) then
    Complex.logarithmicPhaseBProcessRightTailBudget t m
  else 0

def Complex.logarithmicPhaseBProcessClippedPacketBudget
    (t : ℝ) (a b m : ℤ) : ℝ :=
  4 / 3 +
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
      2 * Complex.logarithmicPhaseBProcessRadius t m +
        Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m

theorem Complex.logarithmicPhaseBProcessClippedWindowLeft_eq
    (t : ℝ) (a m : ℤ) :
    Complex.logarithmicPhaseBProcessClippedWindowLeft t a m =
      max (a : ℝ) (Complex.logarithmicPhaseBProcessWindowLeft t m) := by
  rfl

theorem Complex.logarithmicPhaseBProcessClippedWindowRight_eq
    (t : ℝ) (b m : ℤ) :
    Complex.logarithmicPhaseBProcessClippedWindowRight t b m =
      min (b : ℝ) (Complex.logarithmicPhaseBProcessWindowRight t m) := by
  rfl

theorem Complex.norm_logarithmicPhaseBProcessClippedLeftTail_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (hcenterLeft :
      (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ‖∫ x in (a : ℝ)..
        Complex.logarithmicPhaseBProcessClippedWindowLeft t a m,
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m := by
  unfold Complex.logarithmicPhaseBProcessClippedLeftTailBudget
  match Classical.em
      ((a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m) with
  | Or.inl hraw =>
      have hbudgetEq :
          (if (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m then
              Complex.logarithmicPhaseBProcessLeftTailBudget t m
            else 0) =
            Complex.logarithmicPhaseBProcessLeftTailBudget t m :=
        if_pos hraw
      have hleftEq :
          Complex.logarithmicPhaseBProcessClippedWindowLeft t a m =
            Complex.logarithmicPhaseBProcessWindowLeft t m := by
        unfold Complex.logarithmicPhaseBProcessClippedWindowLeft
        unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
        exact max_eq_right hraw
      have haPos : 0 < (a : ℝ) :=
        Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
      have hcenter :=
        Complex.logarithmicPhaseBProcessWindowLeft_lt_center t ht hm
      have htail :=
        Complex.norm_intervalIntegral_logarithmicPhase_leftOfStationary_le_twice_reciprocalGap
          t ht ht_nonneg m hm (a : ℝ)
          (Complex.logarithmicPhaseBProcessWindowLeft t m)
          haPos hraw hcenter
      have hclippedTail :
          ‖∫ x in (a : ℝ)..
              Complex.logarithmicPhaseBProcessClippedWindowLeft t a m,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤
            Complex.logarithmicPhaseBProcessLeftTailBudget t m :=
        Eq.subst
        (motive := fun right : ℝ =>
          ‖∫ x in (a : ℝ)..right,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤
            Complex.logarithmicPhaseBProcessLeftTailBudget t m)
        hleftEq.symm htail
      exact Eq.subst
        (motive := fun budget : ℝ =>
          ‖∫ x in (a : ℝ)..
              Complex.logarithmicPhaseBProcessClippedWindowLeft t a m,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ budget)
        hbudgetEq.symm hclippedTail
  | Or.inr hraw =>
      have hbudgetEq :
          (if (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m then
              Complex.logarithmicPhaseBProcessLeftTailBudget t m
            else 0) = 0 :=
        if_neg hraw
      have hrawLe :
          Complex.logarithmicPhaseBProcessWindowLeft t m ≤ (a : ℝ) :=
        le_of_not_ge hraw
      have hleftEq :
          Complex.logarithmicPhaseBProcessClippedWindowLeft t a m = (a : ℝ) := by
        unfold Complex.logarithmicPhaseBProcessClippedWindowLeft
        unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
        exact max_eq_left hrawLe
      have hzero :
          (∫ x in (a : ℝ)..(a : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x) = 0 :=
        intervalIntegral.integral_same
      have hnormZero :
          ‖∫ x in (a : ℝ)..(a : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ = 0 :=
        (congrArg norm hzero).trans norm_zero
      have hclippedTail :
          ‖∫ x in (a : ℝ)..
              Complex.logarithmicPhaseBProcessClippedWindowLeft t a m,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ 0 :=
        Eq.subst
        (motive := fun right : ℝ =>
          ‖∫ x in (a : ℝ)..right,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ 0)
        hleftEq.symm
        (le_of_eq hnormZero)
      exact Eq.subst
        (motive := fun budget : ℝ =>
          ‖∫ x in (a : ℝ)..
              Complex.logarithmicPhaseBProcessClippedWindowLeft t a m,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ budget)
        hbudgetEq.symm hclippedTail

theorem Complex.norm_logarithmicPhaseBProcessClippedRightTail_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (hcenterRight :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ)) :
    ‖∫ x in Complex.logarithmicPhaseBProcessClippedWindowRight t b m..(b : ℝ),
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m := by
  unfold Complex.logarithmicPhaseBProcessClippedRightTailBudget
  match Classical.em
      (Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ)) with
  | Or.inl hraw =>
      have hbudgetEq :
          (if Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) then
              Complex.logarithmicPhaseBProcessRightTailBudget t m
            else 0) =
            Complex.logarithmicPhaseBProcessRightTailBudget t m :=
        if_pos hraw
      have hrightEq :
          Complex.logarithmicPhaseBProcessClippedWindowRight t b m =
            Complex.logarithmicPhaseBProcessWindowRight t m := by
        unfold Complex.logarithmicPhaseBProcessClippedWindowRight
        unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
        exact min_eq_right hraw
      have hcenterPos :=
        Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
      have hrightPos := lt_of_lt_of_le hcenterPos
        (Complex.logarithmicPhaseBProcess_center_lt_WindowRight t ht hm).le
      have hcenter :=
        Complex.logarithmicPhaseBProcess_center_lt_WindowRight t ht hm
      have htail :=
        Complex.norm_intervalIntegral_logarithmicPhase_rightOfStationary_le_twice_reciprocalGap
          t ht ht_nonneg m hm
          (Complex.logarithmicPhaseBProcessWindowRight t m) (b : ℝ)
          hrightPos hraw hcenter
      have hclippedTail :
          ‖∫ x in Complex.logarithmicPhaseBProcessClippedWindowRight t b m..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤
            Complex.logarithmicPhaseBProcessRightTailBudget t m :=
        Eq.subst
        (motive := fun left : ℝ =>
          ‖∫ x in left..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤
            Complex.logarithmicPhaseBProcessRightTailBudget t m)
        hrightEq.symm htail
      exact Eq.subst
        (motive := fun budget : ℝ =>
          ‖∫ x in Complex.logarithmicPhaseBProcessClippedWindowRight t b m..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ budget)
        hbudgetEq.symm hclippedTail
  | Or.inr hraw =>
      have hbudgetEq :
          (if Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) then
              Complex.logarithmicPhaseBProcessRightTailBudget t m
            else 0) = 0 :=
        if_neg hraw
      have hrawLe :
          (b : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowRight t m :=
        le_of_not_ge hraw
      have hrightEq :
          Complex.logarithmicPhaseBProcessClippedWindowRight t b m = (b : ℝ) := by
        unfold Complex.logarithmicPhaseBProcessClippedWindowRight
        unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
        exact min_eq_left hrawLe
      have hzero :
          (∫ x in (b : ℝ)..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x) = 0 :=
        intervalIntegral.integral_same
      have hnormZero :
          ‖∫ x in (b : ℝ)..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ = 0 :=
        (congrArg norm hzero).trans norm_zero
      have hclippedTail :
          ‖∫ x in Complex.logarithmicPhaseBProcessClippedWindowRight t b m..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ 0 :=
        Eq.subst
        (motive := fun left : ℝ =>
          ‖∫ x in left..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ 0)
        hrightEq.symm
        (le_of_eq hnormZero)
      exact Eq.subst
        (motive := fun budget : ℝ =>
          ‖∫ x in Complex.logarithmicPhaseBProcessClippedWindowRight t b m..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ budget)
        hbudgetEq.symm hclippedTail

theorem Complex.norm_logarithmicPhaseBProcessClippedCentral_le_two_radius
    (t : ℝ) (a b m : ℤ)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m ∈
        Set.Icc (a : ℝ) (b : ℝ))
    (hradius : 0 ≤ Complex.logarithmicPhaseBProcessRadius t m) :
    ‖∫ x in Complex.logarithmicPhaseBProcessClippedWindowLeft t a m..
        Complex.logarithmicPhaseBProcessClippedWindowRight t b m,
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      2 * Complex.logarithmicPhaseBProcessRadius t m := by
  exact
    Complex.norm_logarithmicPhaseQuantitativeEndpointCentral_le_two_radius
      t a b m
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
      hcenter hradius

theorem Complex.norm_logarithmicPhaseBProcessClippedPrincipal_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m ∈
        Set.Icc (a : ℝ) (b : ℝ)) :
    ‖∫ x in (a : ℝ)..(b : ℝ),
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
        2 * Complex.logarithmicPhaseBProcessRadius t m +
          Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m := by
  have hradius :=
    Complex.logarithmicPhaseBProcessRadius_nonneg t ht hm
  have hleft :=
    Complex.norm_logarithmicPhaseBProcessClippedLeftTail_le
      t ht ht_nonneg a b m ha hab hm hcenter.1
  have hright :=
    Complex.norm_logarithmicPhaseBProcessClippedRightTail_le
      t ht ht_nonneg a b m ha hab hm hcenter.2
  have hcentral :=
    Complex.norm_logarithmicPhaseBProcessClippedCentral_le_two_radius
      t a b m hcenter hradius
  have hleftBound :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowLeft_ge_blockLeft
      a (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
  have hrightBound :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowRight_le_blockRight
      b (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
  have hwindowOrder :=
    Complex.logarithmicPhaseQuantitativeEndpointWindow_nonempty
      a b (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m) hcenter hradius
  exact
    Complex.norm_logarithmicPhaseQuantitativeEndpoint_principal_le
      t ht_nonneg a b m
      (Complex.logarithmicPhaseBProcessClippedWindowLeft t a m)
      (Complex.logarithmicPhaseBProcessClippedWindowRight t b m)
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
      ha hleftBound hwindowOrder hrightBound hleft hright hcentral

theorem Complex.norm_integerBlockFourierPacket_le_BProcessClippedPacketBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m ∈
        Set.Icc (a : ℝ) (b : ℝ)) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      Complex.logarithmicPhaseBProcessClippedPacketBudget t a b m := by
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessClippedPrincipal_le
      t ht ht_nonneg a b m ha hab hm hcenter
  have hpacket :=
    Complex.norm_integerBlockFourierPacket_le_crossing_add_principal
      t a b m ha hab hprincipal
  have hbudgetEq :
      Complex.logarithmicPhaseBProcessClippedPacketBudget t a b m =
        4 / 3 +
          (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
            2 * Complex.logarithmicPhaseBProcessRadius t m +
              Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m) := by
    unfold Complex.logarithmicPhaseBProcessClippedPacketBudget
    have hfirstAssociation :
        (4 / 3 + Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m) +
              2 * Complex.logarithmicPhaseBProcessRadius t m =
          4 / 3 +
            (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
              2 * Complex.logarithmicPhaseBProcessRadius t m) :=
      add_assoc
        (4 / 3)
        (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m)
        (2 * Complex.logarithmicPhaseBProcessRadius t m)
    have hfirstAssociationWithRight :
        ((4 / 3 + Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m) +
              2 * Complex.logarithmicPhaseBProcessRadius t m) +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m =
          (4 / 3 +
            (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
              2 * Complex.logarithmicPhaseBProcessRadius t m)) +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m :=
      congrArg
        (fun value : ℝ =>
          value + Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m)
        hfirstAssociation
    have hsecondAssociation :
        (4 / 3 +
            (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
              2 * Complex.logarithmicPhaseBProcessRadius t m)) +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m =
          4 / 3 +
            ((Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
              2 * Complex.logarithmicPhaseBProcessRadius t m) +
              Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m) :=
      add_assoc
        (4 / 3)
        (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
          2 * Complex.logarithmicPhaseBProcessRadius t m)
        (Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m)
    exact Eq.trans hfirstAssociationWithRight hsecondAssociation
  exact Eq.subst
    (motive := fun budget : ℝ =>
      ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ budget)
    hbudgetEq.symm hpacket

end

end LFunctions
end Boundary
