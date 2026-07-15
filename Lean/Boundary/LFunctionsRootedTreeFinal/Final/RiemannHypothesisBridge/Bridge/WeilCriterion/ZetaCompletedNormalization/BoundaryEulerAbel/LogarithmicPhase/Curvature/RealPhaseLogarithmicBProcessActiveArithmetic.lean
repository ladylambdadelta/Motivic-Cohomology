import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessPacketArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicLongGeometry

/-!
# Active-family arithmetic for the balanced logarithmic B-process

The analytic owner bounds each interior packet by one endpoint majorant.  This
file lifts that inequality through the finite mode sum, replaces the interior
cardinality by the enclosing mode-range cardinality, and finally substitutes
the explicit real mode-range majorant.  The resulting expression is entirely
scalar and is the input to the long-geometry regime split.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseBProcessScale_nonneg
    (t : ℝ) :
    0 ≤ Complex.logarithmicPhaseBProcessScale t :=
  (Complex.logarithmicPhaseBProcessScale_pos t).le

theorem Complex.logarithmicPhaseBProcess_norm_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    0 < ‖t‖ :=
  lt_of_lt_of_le zero_lt_one ht

theorem Complex.logarithmicPhaseBProcess_endpoint_mul_scale_div_norm_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {b : ℤ} (hb : 0 ≤ b) :
    0 ≤ (b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ := by
  have hbReal : 0 ≤ (b : ℝ) := Int.cast_nonneg.mpr hb
  exact div_nonneg
    (mul_nonneg hbReal
      (Complex.logarithmicPhaseBProcessScale_nonneg t))
    (norm_nonneg t)

theorem Complex.logarithmicPhaseBProcess_endpoint_div_scale_nonneg
    (t : ℝ) {b : ℤ} (hb : 0 ≤ b) :
    0 ≤ (b : ℝ) / Complex.logarithmicPhaseBProcessScale t := by
  exact div_nonneg
    (Int.cast_nonneg.mpr hb)
    (Complex.logarithmicPhaseBProcessScale_nonneg t)

theorem Complex.logarithmicPhaseBProcessPerModeEndpointMajorant_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {b : ℤ} (hb : 0 ≤ b) :
    0 ≤ Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b := by
  unfold Complex.logarithmicPhaseBProcessPerModeEndpointMajorant
  have hcrossing : 0 ≤ (4 / 3 : ℝ) :=
    div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3)
  have htail :
      0 ≤ 2 * ((b : ℝ) *
        Complex.logarithmicPhaseBProcessScale t / ‖t‖) :=
    mul_nonneg zero_le_two
      (Complex.logarithmicPhaseBProcess_endpoint_mul_scale_div_norm_nonneg
        t ht hb)
  have hcentral :
      0 ≤ 2 * ((b : ℝ) /
        Complex.logarithmicPhaseBProcessScale t) :=
    mul_nonneg zero_le_two
      (Complex.logarithmicPhaseBProcess_endpoint_div_scale_nonneg
        t hb)
  exact add_nonneg (add_nonneg (add_nonneg hcrossing htail) hcentral) htail

theorem Complex.logarithmicPhaseBProcessInteriorBudget_le_sum_endpointMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) :
    Complex.logarithmicPhaseBProcessInteriorBudget t a b ≤
      ∑ _m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
        Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b := by
  have hsumMajorants :=
    Complex.sum_logarithmicPhaseBProcessStationaryPacketMajorant_eq_budget
      t a b
  have hpointwise :
      (∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
        Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m) ≤
        ∑ _m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
          Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b := by
    exact Finset.sum_le_sum (fun m hm =>
      Complex.logarithmicPhaseBProcessStationaryPacketMajorant_le_endpointMajorant
        t ht hm)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤
        ∑ _m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
          Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b)
    hsumMajorants
    hpointwise

theorem Complex.sum_logarithmicPhaseBProcessPerModeEndpointMajorant_eq_card_mul
    (t : ℝ) (a b : ℤ) :
    (∑ _m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
      Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b) =
      ((Complex.logarithmicPhasePoissonBProcessInteriorModes t a b).card : ℝ) *
        Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b := by
  exact Finset.sum_const_real_eq_card_mul
    (Complex.logarithmicPhasePoissonBProcessInteriorModes t a b)
    (Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b)

theorem Complex.logarithmicPhaseBProcessInteriorBudget_le_card_mul_endpointMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) :
    Complex.logarithmicPhaseBProcessInteriorBudget t a b ≤
      ((Complex.logarithmicPhasePoissonBProcessInteriorModes t a b).card : ℝ) *
        Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b := by
  have hsum :=
    Complex.logarithmicPhaseBProcessInteriorBudget_le_sum_endpointMajorant
      t ht a b
  exact hsum.trans_eq
    (Complex.sum_logarithmicPhaseBProcessPerModeEndpointMajorant_eq_card_mul
      t a b)

theorem Complex.logarithmicPhaseBProcessInterior_card_real_le_modeRange_card
    (t : ℝ) (a b : ℤ) :
    ((Complex.logarithmicPhasePoissonBProcessInteriorModes t a b).card : ℝ) ≤
      ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) := by
  exact Nat.cast_le.mpr
    (Complex.logarithmicPhasePoissonBProcessInteriorModes_card_le_modeRange
      t a b)

theorem Complex.logarithmicPhaseBProcessInteriorBudget_le_modeRangeCard_mul_endpointMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (hb : 0 ≤ b) :
    Complex.logarithmicPhaseBProcessInteriorBudget t a b ≤
      ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) *
        Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b := by
  have hbudget :=
    Complex.logarithmicPhaseBProcessInteriorBudget_le_card_mul_endpointMajorant
      t ht a b
  have hcard :=
    Complex.logarithmicPhaseBProcessInterior_card_real_le_modeRange_card
      t a b
  have hmajorantNonneg :=
    Complex.logarithmicPhaseBProcessPerModeEndpointMajorant_nonneg
      t ht hb
  have hscaled :=
    mul_le_mul_of_nonneg_right hcard hmajorantNonneg
  exact le_trans hbudget hscaled

theorem Complex.logarithmicPhaseBProcessInteriorBudget_le_cardMajorant_mul_endpointMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    Complex.logarithmicPhaseBProcessInteriorBudget t a b ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a *
        Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b := by
  have hbudget :=
    Complex.logarithmicPhaseBProcessInteriorBudget_le_modeRangeCard_mul_endpointMajorant
      t ht a b hb
  have hcard :=
    Complex.logarithmicPhasePoissonModeRange_card_real_le_majorant
      t a ha
  have hmajorantNonneg :=
    Complex.logarithmicPhaseBProcessPerModeEndpointMajorant_nonneg
      t ht hb
  have hscaled :=
    mul_le_mul_of_nonneg_right hcard hmajorantNonneg
  exact le_trans hbudget hscaled

def Complex.logarithmicPhaseBProcessClosedInteriorMajorant
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseModeRangeCardMajorant t a *
    Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b

theorem Complex.logarithmicPhaseBProcessInteriorBudget_le_closedMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    Complex.logarithmicPhaseBProcessInteriorBudget t a b ≤
      Complex.logarithmicPhaseBProcessClosedInteriorMajorant t a b := by
  exact
    Complex.logarithmicPhaseBProcessInteriorBudget_le_cardMajorant_mul_endpointMajorant
      t ht a b ha hb

theorem Complex.logarithmicPhaseBProcessClosedInteriorMajorant_eq_explicit
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant t a b =
      (2 + ‖t‖ /
        (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a)) *
      (4 / 3 +
        2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) +
        2 * ((b : ℝ) / Complex.logarithmicPhaseBProcessScale t) +
        2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖)) := by
  rfl

theorem Complex.norm_logarithmicPhaseBProcessInterior_packet_tsum_le_closedMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : 0 ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhaseBProcessClosedInteriorMajorant t a b := by
  have hanalytic :=
    Complex.norm_logarithmicPhaseBProcessInterior_packet_tsum_le_budget
      t ht ht_nonneg a b ha hab
  have harithmetic :=
    Complex.logarithmicPhaseBProcessInteriorBudget_le_closedMajorant
      t ht a b ha hb
  exact le_trans hanalytic harithmetic

theorem Complex.logarithmicPhaseBProcessClosedInteriorMajorant_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    0 ≤ Complex.logarithmicPhaseBProcessClosedInteriorMajorant t a b := by
  have hcardNonneg :
      0 ≤ Complex.logarithmicPhaseModeRangeCardMajorant t a := by
    unfold Complex.logarithmicPhaseModeRangeCardMajorant
    have hleftPos := Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
    have hdenominatorPos :
        0 < 2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a :=
      mul_pos Complex.two_mul_pi_pos hleftPos
    have hquotient :
        0 ≤ ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) :=
      div_nonneg (norm_nonneg t) hdenominatorPos.le
    exact add_nonneg zero_le_two hquotient
  have hpacketNonneg :=
    Complex.logarithmicPhaseBProcessPerModeEndpointMajorant_nonneg
      t ht hb
  unfold Complex.logarithmicPhaseBProcessClosedInteriorMajorant
  exact mul_nonneg hcardNonneg hpacketNonneg

end

end LFunctions
end Boundary
