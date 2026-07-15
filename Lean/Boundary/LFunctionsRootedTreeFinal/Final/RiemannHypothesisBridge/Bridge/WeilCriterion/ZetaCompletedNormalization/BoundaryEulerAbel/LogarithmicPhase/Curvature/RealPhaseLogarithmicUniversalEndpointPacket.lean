import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointWindowGeometry

/-!
# Universal clipped estimate for balanced endpoint packets

The clipped balanced window is valid for every endpoint mode, including modes
whose stationary center lies in a cutoff collar outside the principal block.
The two tails are either empty or begin at a genuine balanced-window endpoint;
the middle interval has length at most twice the balanced radius.  This owner
therefore replaces the singular outside-center estimate by one uniform packet
budget on the original single-counted endpoint family.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
    (t : ℝ) (a b m : ℤ) : ℝ :=
  4 / 3 +
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
      2 * Complex.logarithmicPhaseBProcessRadius t m +
        Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m

def Complex.logarithmicPhaseBProcessUniversalEndpointBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b,
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_eq_clipped
    (t : ℝ) (a b m : ℤ) :
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m =
      Complex.logarithmicPhaseBProcessClippedPacketBudget t a b m := by
  rfl

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_eq_crossing_add
    (t : ℝ) (a b m : ℤ) :
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m =
      4 / 3 +
        (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
          2 * Complex.logarithmicPhaseBProcessRadius t m +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m) := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
  have hfirst :
      (4 / 3 +
          Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m) +
          2 * Complex.logarithmicPhaseBProcessRadius t m =
        4 / 3 +
          (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
            2 * Complex.logarithmicPhaseBProcessRadius t m) :=
    add_assoc _ _ _
  have hwithRight := congrArg
    (fun value : ℝ =>
      value + Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m)
    hfirst
  exact Eq.trans hwithRight
    (add_assoc
      (4 / 3 : ℝ)
      (Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
        2 * Complex.logarithmicPhaseBProcessRadius t m)
      (Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m))

theorem Complex.norm_logarithmicPhaseBProcessUniversalLeftTail_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0) :
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
      have hclippedTail := Eq.subst
        (motive := fun right : ℝ =>
          ‖∫ x in (a : ℝ)..right,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤
            Complex.logarithmicPhaseBProcessLeftTailBudget t m)
        hleftEq.symm htail
      have hbudget :
          (if (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m then
              Complex.logarithmicPhaseBProcessLeftTailBudget t m else 0) =
            Complex.logarithmicPhaseBProcessLeftTailBudget t m :=
        if_pos hraw
      exact hclippedTail.trans_eq hbudget.symm
  | Or.inr hraw =>
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
      have hclippedZero := Eq.subst
        (motive := fun right : ℝ =>
          ‖∫ x in (a : ℝ)..right,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ 0)
        hleftEq.symm (le_of_eq hnormZero)
      have hbudget :
          (if (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m then
              Complex.logarithmicPhaseBProcessLeftTailBudget t m else 0) = 0 :=
        if_neg hraw
      exact hclippedZero.trans_eq hbudget.symm

theorem Complex.norm_logarithmicPhaseBProcessUniversalRightTail_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0) :
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
      have hclippedTail := Eq.subst
        (motive := fun left : ℝ =>
          ‖∫ x in left..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤
            Complex.logarithmicPhaseBProcessRightTailBudget t m)
        hrightEq.symm htail
      have hbudget :
          (if Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) then
              Complex.logarithmicPhaseBProcessRightTailBudget t m else 0) =
            Complex.logarithmicPhaseBProcessRightTailBudget t m :=
        if_pos hraw
      exact hclippedTail.trans_eq hbudget.symm
  | Or.inr hraw =>
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
      have hclippedZero := Eq.subst
        (motive := fun left : ℝ =>
          ‖∫ x in left..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ ≤ 0)
        hrightEq.symm (le_of_eq hnormZero)
      have hbudget :
          (if Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) then
              Complex.logarithmicPhaseBProcessRightTailBudget t m else 0) = 0 :=
        if_neg hraw
      exact hclippedZero.trans_eq hbudget.symm

theorem Complex.norm_logarithmicPhaseBProcessUniversalCentral_le_two_radius
    (t : ℝ) (a b m : ℤ)
    (horder :
      Complex.logarithmicPhaseBProcessClippedWindowLeft t a m ≤
        Complex.logarithmicPhaseBProcessClippedWindowRight t b m) :
    ‖∫ x in Complex.logarithmicPhaseBProcessClippedWindowLeft t a m..
        Complex.logarithmicPhaseBProcessClippedWindowRight t b m,
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      2 * Complex.logarithmicPhaseBProcessRadius t m := by
  have hlength :=
    Complex.norm_intervalIntegral_realPhaseOscillation_le_length
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m)
      (Complex.logarithmicPhaseBProcessClippedWindowLeft t a m)
      (Complex.logarithmicPhaseBProcessClippedWindowRight t b m)
      horder
  have hwidth :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowWidth_le_two_radius
      a b
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
  exact le_trans hlength hwidth

theorem Complex.norm_logarithmicPhaseBProcessUniversalPrincipal_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (horder :
      Complex.logarithmicPhaseBProcessClippedWindowLeft t a m ≤
        Complex.logarithmicPhaseBProcessClippedWindowRight t b m) :
    ‖∫ x in (a : ℝ)..(b : ℝ),
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
        2 * Complex.logarithmicPhaseBProcessRadius t m +
          Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m := by
  have hleft :=
    Complex.norm_logarithmicPhaseBProcessUniversalLeftTail_le
      t ht ht_nonneg a b m ha hab hm
  have hright :=
    Complex.norm_logarithmicPhaseBProcessUniversalRightTail_le
      t ht ht_nonneg a b m ha hab hm
  have hcentral :=
    Complex.norm_logarithmicPhaseBProcessUniversalCentral_le_two_radius
      t a b m horder
  have hleftBound :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowLeft_ge_blockLeft
      a (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
  have hrightBound :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowRight_le_blockRight
      b (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
  exact
    Complex.norm_logarithmicPhaseQuantitativeEndpoint_principal_le
      t ht_nonneg a b m
      (Complex.logarithmicPhaseBProcessClippedWindowLeft t a m)
      (Complex.logarithmicPhaseBProcessClippedWindowRight t b m)
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
      ha hleftBound horder hrightBound hleft hright hcentral

theorem Complex.norm_integerBlockFourierPacket_le_BProcessUniversalEndpointBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (horder :
      Complex.logarithmicPhaseBProcessClippedWindowLeft t a m ≤
        Complex.logarithmicPhaseBProcessClippedWindowRight t b m) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m := by
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessUniversalPrincipal_le
      t ht ht_nonneg a b m ha hab hm horder
  have hpacket :=
    Complex.norm_integerBlockFourierPacket_le_crossing_add_principal
      t a b m ha hab hprincipal
  exact hpacket.trans_eq
    (Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_eq_crossing_add
      t a b m).symm

theorem Complex.norm_endpointMode_integerBlockFourierPacket_le_universalBudget
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
        t (a : ℤ) (b : ℤ) m := by
  have ha : (1 : ℤ) ≤ (a : ℤ) :=
    Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab : (a : ℤ) ≤ (b : ℤ) :=
    Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hmNeg :=
    Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm
  have horder :=
    Complex.logarithmicPhaseBProcessEndpointMode_clippedWindow_order
      hgeometry hm
  exact
    Complex.norm_integerBlockFourierPacket_le_BProcessUniversalEndpointBudget
      t ht ht_nonneg (a : ℤ) (b : ℤ) m ha hab hmNeg horder

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_nonneg
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    0 ≤ Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
      t (a : ℤ) (b : ℤ) m := by
  have hpacket :=
    Complex.norm_endpointMode_integerBlockFourierPacket_le_universalBudget
      ht ht_nonneg hgeometry hm
  exact le_trans (norm_nonneg _) hpacket

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_nonneg
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 ≤ Complex.logarithmicPhaseBProcessUniversalEndpointBudget
      t (a : ℤ) (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointBudget
  exact Finset.sum_nonneg (fun m hm =>
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_nonneg
      ht ht_nonneg hgeometry hm)

theorem Complex.norm_logarithmicPhaseBProcessEndpoint_packet_tsum_le_universalBudget
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
          t (a : ℤ) (b : ℤ)},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) := by
  exact
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t (a : ℤ) (b : ℤ)
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ))
      (Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
        t (a : ℤ) (b : ℤ))
      (fun m hm =>
        Complex.norm_endpointMode_integerBlockFourierPacket_le_universalBudget
          ht ht_nonneg hgeometry hm)

end

end LFunctions
end Boundary
