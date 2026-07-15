import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveFarReciprocalGeometry

/-!
# Arithmetic closure of finite far reciprocal gaps

Balanced separation supplies a uniform reciprocal endpoint majorant for every
far mode.  This owner proves the exact normalization, the two packetwise
estimates, and the finite-family sums.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
    (t : ℝ) (a : ℤ) : ℝ :=
  2 * ((a : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖)

def Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant
    (t : ℝ) (b : ℤ) : ℝ :=
  2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖)

def Complex.logarithmicPhaseFiniteFarCardinalityReciprocalMajorant
    (t : ℝ) (a b : ℤ) : ℝ :=
  ((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card : ℝ) *
      Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant t a +
    ((Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℝ) *
      Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant t b

theorem Complex.logarithmicPhaseFiniteFar_radiusGap_eq_norm_div_scale_div_endpoint
    (t : ℝ) {m : ℤ} (hm : m < 0) {x : ℝ} :
    (2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhaseBProcessRadius t m / x =
      (‖t‖ / Complex.logarithmicPhaseBProcessScale t) / x := by
  have hangular :=
    Complex.logarithmicPhaseBProcess_angular_mul_radius_eq_norm_div_scale
      t hm
  exact congrArg (fun value : ℝ => value / x) hangular

theorem Complex.logarithmicPhaseFiniteFar_inv_radiusGap_eq_endpoint_mul_scale_div_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0)
    {x : ℝ} (hx : 0 < x) :
    ((2 * Real.pi * (-(m : ℝ))) *
        Complex.logarithmicPhaseBProcessRadius t m / x)⁻¹ =
      x * Complex.logarithmicPhaseBProcessScale t / ‖t‖ := by
  have hgap :=
    Complex.logarithmicPhaseFiniteFar_radiusGap_eq_norm_div_scale_div_endpoint
      t hm (x := x)
  exact Eq.trans (congrArg Inv.inv hgap)
    (Real.inv_div_div_eq_mul_div
      ‖t‖ (Complex.logarithmicPhaseBProcessScale t) x
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ht))
      (Complex.logarithmicPhaseBProcessScale_ne_zero t)
      (ne_of_gt hx))

theorem Complex.logarithmicPhaseFiniteLeftFar_derivative_pos
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    0 < Complex.logarithmicPhaseFourierTwistedDerivative t m (a : ℝ) := by
  have hmNeg := Complex.logarithmicPhaseFiniteLeftFar_mode_neg hm
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  exact
    Complex.logarithmicPhaseFourierTwistedDerivative_pos_of_gt_stationaryPoint
      t hmNeg haPos
      (Complex.logarithmicPhaseFiniteLeftFar_center_lt_endpoint ht hm)

theorem Complex.logarithmicPhaseFiniteRightFar_derivative_neg
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (hb : 1 ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    Complex.logarithmicPhaseFourierTwistedDerivative t m (b : ℝ) < 0 := by
  have hmNeg := Complex.logarithmicPhaseFiniteRightFar_mode_neg hm
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  exact
    Complex.logarithmicPhaseFourierTwistedDerivative_neg_of_lt_stationaryPoint
      t hmNeg hbPos
      (Complex.logarithmicPhaseFiniteRightFar_endpoint_lt_center hm)

theorem Complex.logarithmicPhaseFiniteLeftFar_radiusGap_pos
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    0 < (2 * Real.pi * (-(m : ℝ))) *
      Complex.logarithmicPhaseBProcessRadius t m / (a : ℝ) := by
  have hmNeg := Complex.logarithmicPhaseFiniteLeftFar_mode_neg hm
  have hangular :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hmNeg
  have hradius :=
    Complex.logarithmicPhaseFiniteLeftFar_radius_pos ht hm
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  exact div_pos (mul_pos hangular hradius) haPos

theorem Complex.logarithmicPhaseFiniteRightFar_radiusGap_pos
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (hb : 1 ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    0 < (2 * Real.pi * (-(m : ℝ))) *
      Complex.logarithmicPhaseBProcessRadius t m / (b : ℝ) := by
  have hmNeg := Complex.logarithmicPhaseFiniteRightFar_mode_neg hm
  have hangular :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hmNeg
  have hradius :=
    Complex.logarithmicPhaseFiniteRightFar_radius_pos ht hm
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  exact div_pos (mul_pos hangular hradius) hbPos

theorem Complex.logarithmicPhaseFiniteLeftFar_reciprocalGap_le_endpoint_majorant
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) ≤
      (a : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ := by
  have hgap :=
    Complex.logarithmicPhaseFiniteLeftFar_derivativeGap_ge_radiusGap
      ht ha hm
  have hbasePos :=
    Complex.logarithmicPhaseFiniteLeftFar_radiusGap_pos ht ha hm
  have hinverse := Real.inv_le_inv_of_pos_le hbasePos hgap
  have hnormalize :=
    Complex.logarithmicPhaseFiniteFar_inv_radiusGap_eq_endpoint_mul_scale_div_norm
      t ht (Complex.logarithmicPhaseFiniteLeftFar_mode_neg hm)
      (Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha))
  unfold Complex.logarithmicPhaseRightReciprocalGap
  exact le_trans hinverse (le_of_eq hnormalize)

theorem Complex.logarithmicPhaseFiniteRightFar_reciprocalGap_le_endpoint_majorant
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (hb : 1 ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) ≤
      (b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ := by
  have hgap :=
    Complex.logarithmicPhaseFiniteRightFar_negDerivativeGap_ge_radiusGap
      ht hb hm
  have hbasePos :=
    Complex.logarithmicPhaseFiniteRightFar_radiusGap_pos ht hb hm
  have hinverse := Real.inv_le_inv_of_pos_le hbasePos hgap
  have hnormalize :=
    Complex.logarithmicPhaseFiniteFar_inv_radiusGap_eq_endpoint_mul_scale_div_norm
      t ht (Complex.logarithmicPhaseFiniteRightFar_mode_neg hm)
      (Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb))
  unfold Complex.logarithmicPhaseLeftReciprocalGap
  exact le_trans hinverse (le_of_eq hnormalize)

theorem Complex.logarithmicPhaseFiniteLeftFar_two_reciprocalGaps_le_perModeMajorant
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
        Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) ≤
      Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant t a := by
  have hsingle :=
    Complex.logarithmicPhaseFiniteLeftFar_reciprocalGap_le_endpoint_majorant
      ht ha hm
  unfold Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
  exact le_trans (add_le_add hsingle hsingle)
    (le_of_eq (two_mul _).symm)

theorem Complex.logarithmicPhaseFiniteRightFar_two_reciprocalGaps_le_perModeMajorant
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (hb : 1 ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
        Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) ≤
      Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant t b := by
  have hsingle :=
    Complex.logarithmicPhaseFiniteRightFar_reciprocalGap_le_endpoint_majorant
      ht hb hm
  unfold Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant
  exact le_trans (add_le_add hsingle hsingle)
    (le_of_eq (two_mul _).symm)

theorem Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_le_card_mul
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) :
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget t a b ≤
      ((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card : ℝ) *
        Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant t a := by
  unfold Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
  exact Finset.sum_le_card_mul_of_pointwise_le
    (Complex.logarithmicPhaseFiniteLeftFarModes t a b)
    (fun m =>
      Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
        Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ))
    (Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant t a)
    (fun m hm =>
      Complex.logarithmicPhaseFiniteLeftFar_two_reciprocalGaps_le_perModeMajorant
        ht ha hm)

theorem Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_card_mul
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget t a b ≤
      ((Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℝ) *
        Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant t b := by
  have hb : 1 ≤ b := le_trans ha hab
  unfold Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
  exact Finset.sum_le_card_mul_of_pointwise_le
    (Complex.logarithmicPhaseFiniteRightFarModes t a b)
    (fun m =>
      Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
        Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ))
    (Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant t b)
    (fun m hm =>
      Complex.logarithmicPhaseFiniteRightFar_two_reciprocalGaps_le_perModeMajorant
        ht hb hm)

theorem Complex.logarithmicPhaseFiniteFarReciprocalBudget_le_cardinalityMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteFarReciprocalBudget t a b ≤
      Complex.logarithmicPhaseFiniteFarCardinalityReciprocalMajorant
        t a b := by
  unfold Complex.logarithmicPhaseFiniteFarReciprocalBudget
  unfold Complex.logarithmicPhaseFiniteFarCardinalityReciprocalMajorant
  exact add_le_add
    (Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_le_card_mul
      t ht a b ha)
    (Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_card_mul
      t ht a b ha hab)

theorem Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget_le_cardinalityMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget t a b ≤
      Complex.logarithmicPhaseFiniteFarCardinalityReciprocalMajorant
        t a b := by
  unfold Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget
  exact
    Complex.logarithmicPhaseFiniteFarReciprocalBudget_le_cardinalityMajorant
      t ht a b ha hab

end

end LFunctions
end Boundary
