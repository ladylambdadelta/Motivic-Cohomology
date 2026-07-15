import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessActiveBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicModeRangeCardinality

/-!
# Arithmetic normalization of balanced logarithmic packets

This owner rewrites the balanced reciprocal-gap budgets in their exact scale
form.  If `x_m` is the stationary center and
`S = sqrt (1 + ‖t‖)`, the balanced radius is `x_m / S`.  The stationary
identity `angularFrequency * x_m = ‖t‖` then gives

* left reciprocal gap  = `leftEndpoint * S / ‖t‖`;
* right reciprocal gap = `rightEndpoint * S / ‖t‖`;
* central width        = `2 * x_m / S`.

The final declarations turn these identities into uniform endpoint bounds for
one interior mode.  Finite-family counting is deliberately left to the next
owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.mul_div_mul_cancel_right
    (a b c : ℝ) (hc : c ≠ 0) :
    (a * c) / (b * c) = a / b := by
  have hinverseProduct : (b * c)⁻¹ = c⁻¹ * b⁻¹ :=
    mul_inv_rev b c
  calc
    (a * c) / (b * c) = (a * c) * (b * c)⁻¹ :=
      div_eq_mul_inv (a * c) (b * c)
    _ = (a * c) * (c⁻¹ * b⁻¹) :=
      congrArg (fun value : ℝ => (a * c) * value) hinverseProduct
    _ = a * (c * c⁻¹) * b⁻¹ := by
      exact Eq.trans
        (mul_assoc (a * c) c⁻¹ b⁻¹).symm
        (congrArg (fun value : ℝ => value * b⁻¹)
          (mul_assoc a c c⁻¹))
    _ = a * 1 * b⁻¹ := by
      exact congrArg (fun value : ℝ => a * value * b⁻¹)
        (mul_inv_cancel₀ hc)
    _ = a * b⁻¹ := by
      exact congrArg (fun value : ℝ => value * b⁻¹) (mul_one a)
    _ = a / b :=
      (div_eq_mul_inv a b).symm

theorem Real.mul_div_assoc_four
    (a b c d : ℝ) :
    (a * b) / c / d = a * b / (c * d) := by
  exact div_div (a * b) c d

theorem Real.div_mul_div_reassociate
    (a b c d : ℝ) :
    (a / b) * c / d = a * c / (b * d) := by
  calc
    (a / b) * c / d = (a * b⁻¹) * c * d⁻¹ := by
      exact congrArg (fun value : ℝ => value * d⁻¹)
        (congrArg (fun value : ℝ => value * c)
          (div_eq_mul_inv a b))
    _ = (a * c) * (b⁻¹ * d⁻¹) := by
      calc
        (a * b⁻¹) * c * d⁻¹ = a * (b⁻¹ * c) * d⁻¹ :=
          congrArg (fun value : ℝ => value * d⁻¹)
            (mul_assoc a b⁻¹ c)
        _ = a * (c * b⁻¹) * d⁻¹ := by
          exact congrArg (fun value : ℝ => a * value * d⁻¹)
            (mul_comm b⁻¹ c)
        _ = (a * c) * b⁻¹ * d⁻¹ := by
          exact congrArg (fun value : ℝ => value * d⁻¹)
            (mul_assoc a c b⁻¹).symm
        _ = (a * c) * (b⁻¹ * d⁻¹) :=
          mul_assoc (a * c) b⁻¹ d⁻¹
    _ = (a * c) * (b * d)⁻¹ := by
      exact congrArg (fun value : ℝ => (a * c) * value)
        (Eq.trans (mul_comm b⁻¹ d⁻¹) (mul_inv_rev b d).symm)
    _ = a * c / (b * d) :=
      (div_eq_mul_inv (a * c) (b * d)).symm

theorem Complex.logarithmicPhaseBProcess_angular_mul_radius_eq_norm_div_scale
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    (2 * Real.pi * (-(m : ℝ))) *
        Complex.logarithmicPhaseBProcessRadius t m =
      ‖t‖ / Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessRadius
  have hstationary :=
    Complex.logarithmicPhaseAngular_mul_stationaryCenter t hm
  have hreassociate :
      (2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m /
            Complex.logarithmicPhaseBProcessScale t) =
        ((2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhaseFourierStationaryPoint t m) /
            Complex.logarithmicPhaseBProcessScale t := by
    exact (mul_div_assoc
      (2 * Real.pi * (-(m : ℝ)))
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessScale t)).symm
  exact hreassociate.trans
    (congrArg
      (fun value : ℝ =>
        value / Complex.logarithmicPhaseBProcessScale t)
      hstationary)

theorem Complex.logarithmicPhaseBProcess_center_sub_left_eq_radius
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseFourierStationaryPoint t m -
        Complex.logarithmicPhaseBProcessWindowLeft t m =
      Complex.logarithmicPhaseBProcessRadius t m := by
  unfold Complex.logarithmicPhaseBProcessWindowLeft
  exact sub_sub_cancel
    (Complex.logarithmicPhaseFourierStationaryPoint t m)
    (Complex.logarithmicPhaseBProcessRadius t m)

theorem Complex.logarithmicPhaseBProcess_right_sub_center_eq_radius
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseBProcessWindowRight t m -
        Complex.logarithmicPhaseFourierStationaryPoint t m =
      Complex.logarithmicPhaseBProcessRadius t m := by
  unfold Complex.logarithmicPhaseBProcessWindowRight
  exact add_sub_cancel_left _ _

theorem Complex.logarithmicPhaseBProcess_leftDerivativeGap_eq_norm_div_scale_div_left
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    (2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhaseBProcessWindowLeft t m) /
        Complex.logarithmicPhaseBProcessWindowLeft t m =
      (‖t‖ / Complex.logarithmicPhaseBProcessScale t) /
        Complex.logarithmicPhaseBProcessWindowLeft t m := by
  have hradius :=
    Complex.logarithmicPhaseBProcess_center_sub_left_eq_radius t m
  have hangular :=
    Complex.logarithmicPhaseBProcess_angular_mul_radius_eq_norm_div_scale
      t hm
  exact congrArg
    (fun value : ℝ =>
      value / Complex.logarithmicPhaseBProcessWindowLeft t m)
    ((congrArg
      (fun radius : ℝ =>
        (2 * Real.pi * (-(m : ℝ))) * radius)
      hradius).trans hangular)

theorem Complex.logarithmicPhaseBProcess_rightDerivativeGap_eq_norm_div_scale_div_right
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    (2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseBProcessWindowRight t m -
          Complex.logarithmicPhaseFourierStationaryPoint t m) /
        Complex.logarithmicPhaseBProcessWindowRight t m =
      (‖t‖ / Complex.logarithmicPhaseBProcessScale t) /
        Complex.logarithmicPhaseBProcessWindowRight t m := by
  have hradius :=
    Complex.logarithmicPhaseBProcess_right_sub_center_eq_radius t m
  have hangular :=
    Complex.logarithmicPhaseBProcess_angular_mul_radius_eq_norm_div_scale
      t hm
  exact congrArg
    (fun value : ℝ =>
      value / Complex.logarithmicPhaseBProcessWindowRight t m)
    ((congrArg
      (fun radius : ℝ =>
        (2 * Real.pi * (-(m : ℝ))) * radius)
      hradius).trans hangular)

theorem Real.inv_div_div_eq_mul_div
    (norm scale endpoint : ℝ)
    (hnorm : norm ≠ 0)
    (hscale : scale ≠ 0)
    (hendpoint : endpoint ≠ 0) :
    ((norm / scale) / endpoint)⁻¹ = endpoint * scale / norm := by
  have hquotient :
      (norm / scale) / endpoint = norm / (scale * endpoint) :=
    div_div norm scale endpoint
  have hdenominator : scale * endpoint ≠ 0 :=
    mul_ne_zero hscale hendpoint
  have hinverseDivision :
      (norm / (scale * endpoint))⁻¹ =
        (scale * endpoint) / norm :=
    inv_div norm (scale * endpoint)
  have hcommute : scale * endpoint = endpoint * scale :=
    mul_comm scale endpoint
  exact
    (congrArg Inv.inv hquotient).trans
      (hinverseDivision.trans
        (congrArg (fun value : ℝ => value / norm) hcommute))

theorem Complex.logarithmicPhaseBProcessLeftReciprocalGap_eq_endpoint_mul_scale_div_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseLeftReciprocalGap t m
        (Complex.logarithmicPhaseBProcessWindowLeft t m) =
      Complex.logarithmicPhaseBProcessWindowLeft t m *
        Complex.logarithmicPhaseBProcessScale t / ‖t‖ := by
  have hleftPos :
      0 < Complex.logarithmicPhaseBProcessWindowLeft t m := by
    have hscaleStrict : 1 < Complex.logarithmicPhaseBProcessScale t := by
      unfold Complex.logarithmicPhaseBProcessScale
      have hnormPos : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
      have honeStrict : (1 : ℝ) < 1 + ‖t‖ := lt_add_of_pos_right 1 hnormPos
      have hsqrtStrict := Real.sqrt_lt_sqrt (le_of_lt zero_lt_one) honeStrict
      exact Eq.mp
        (congrArg
          (fun value : ℝ => value < Real.sqrt (1 + ‖t‖))
          Real.sqrt_one)
        hsqrtStrict
    unfold Complex.logarithmicPhaseBProcessWindowLeft
    unfold Complex.logarithmicPhaseBProcessRadius
    have hcenterPos :=
      Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
    have hratio :
        Complex.logarithmicPhaseFourierStationaryPoint t m /
            Complex.logarithmicPhaseBProcessScale t <
          Complex.logarithmicPhaseFourierStationaryPoint t m :=
      (div_lt_iff₀ (Complex.logarithmicPhaseBProcessScale_pos t)).mpr (by
        have hscaled := mul_lt_mul_of_pos_left hscaleStrict hcenterPos
        exact lt_of_eq_of_lt
          (mul_one
            (Complex.logarithmicPhaseFourierStationaryPoint t m)).symm
          hscaled)
    exact sub_pos.mpr hratio
  have hphaseGap :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_eq_positiveFrequencyGap
      t hm hleftPos
  have hleftOfCenter :=
    Complex.logarithmicPhaseBProcessWindowLeft_lt_center t ht hm
  have habsDistance :
      |Complex.logarithmicPhaseBProcessWindowLeft t m -
          Complex.logarithmicPhaseFourierStationaryPoint t m| =
        Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhaseBProcessWindowLeft t m :=
    Eq.trans
      (abs_of_nonpos (sub_nonpos.mpr hleftOfCenter.le))
      (neg_sub
        (Complex.logarithmicPhaseBProcessWindowLeft t m)
        (Complex.logarithmicPhaseFourierStationaryPoint t m))
  have hgap :=
    (congrArg
      (fun distance : ℝ =>
        (2 * Real.pi * (-(m : ℝ))) * distance /
          Complex.logarithmicPhaseBProcessWindowLeft t m)
      habsDistance).trans
      (Complex.logarithmicPhaseBProcess_leftDerivativeGap_eq_norm_div_scale_div_left
        t hm)
  unfold Complex.logarithmicPhaseLeftReciprocalGap
  have hderivativeAbs :
      ‖Complex.logarithmicPhaseFourierTwistedDerivative t m
          (Complex.logarithmicPhaseBProcessWindowLeft t m)‖ =
        (‖t‖ / Complex.logarithmicPhaseBProcessScale t) /
          Complex.logarithmicPhaseBProcessWindowLeft t m :=
    hphaseGap.trans hgap
  have hnegative :=
    Complex.logarithmicPhaseFourierTwistedDerivative_neg_of_lt_stationaryPoint
      t hm hleftPos hleftOfCenter
  have habsNeg :
      ‖Complex.logarithmicPhaseFourierTwistedDerivative t m
          (Complex.logarithmicPhaseBProcessWindowLeft t m)‖ =
        -Complex.logarithmicPhaseFourierTwistedDerivative t m
          (Complex.logarithmicPhaseBProcessWindowLeft t m) :=
    Real.norm_of_nonpos hnegative.le
  have hdenominatorEq := habsNeg.symm.trans hderivativeAbs
  have hinverse := congrArg Inv.inv hdenominatorEq
  exact hinverse.trans
    (Real.inv_div_div_eq_mul_div
      ‖t‖ (Complex.logarithmicPhaseBProcessScale t)
      (Complex.logarithmicPhaseBProcessWindowLeft t m)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ht))
      (Complex.logarithmicPhaseBProcessScale_ne_zero t)
      (ne_of_gt hleftPos))

theorem Complex.logarithmicPhaseBProcessRightReciprocalGap_eq_endpoint_mul_scale_div_norm
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseRightReciprocalGap t m
        (Complex.logarithmicPhaseBProcessWindowRight t m) =
      Complex.logarithmicPhaseBProcessWindowRight t m *
        Complex.logarithmicPhaseBProcessScale t / ‖t‖ := by
  have hcenterPos :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hrightPos :
      0 < Complex.logarithmicPhaseBProcessWindowRight t m :=
    lt_of_lt_of_le hcenterPos
      (Complex.logarithmicPhaseBProcess_center_lt_WindowRight
        t ht hm).le
  have hphaseGap :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_eq_positiveFrequencyGap
      t hm hrightPos
  have hrightOfCenter :=
    Complex.logarithmicPhaseBProcess_center_lt_WindowRight t ht hm
  have habsDistance :
      |Complex.logarithmicPhaseBProcessWindowRight t m -
          Complex.logarithmicPhaseFourierStationaryPoint t m| =
        Complex.logarithmicPhaseBProcessWindowRight t m -
          Complex.logarithmicPhaseFourierStationaryPoint t m :=
    abs_of_nonneg (sub_nonneg.mpr hrightOfCenter.le)
  have hgap :=
    (congrArg
      (fun distance : ℝ =>
        (2 * Real.pi * (-(m : ℝ))) * distance /
          Complex.logarithmicPhaseBProcessWindowRight t m)
      habsDistance).trans
      (Complex.logarithmicPhaseBProcess_rightDerivativeGap_eq_norm_div_scale_div_right
        t hm)
  unfold Complex.logarithmicPhaseRightReciprocalGap
  have hderivativeAbs :
      ‖Complex.logarithmicPhaseFourierTwistedDerivative t m
          (Complex.logarithmicPhaseBProcessWindowRight t m)‖ =
        (‖t‖ / Complex.logarithmicPhaseBProcessScale t) /
          Complex.logarithmicPhaseBProcessWindowRight t m :=
    hphaseGap.trans hgap
  have hpositive :=
    Complex.logarithmicPhaseFourierTwistedDerivative_pos_of_gt_stationaryPoint
      t hm hrightPos hrightOfCenter
  have habsPos :
      ‖Complex.logarithmicPhaseFourierTwistedDerivative t m
          (Complex.logarithmicPhaseBProcessWindowRight t m)‖ =
        Complex.logarithmicPhaseFourierTwistedDerivative t m
          (Complex.logarithmicPhaseBProcessWindowRight t m) :=
    Real.norm_of_nonneg hpositive.le
  have hdenominatorEq := habsPos.symm.trans hderivativeAbs
  have hinverse := congrArg Inv.inv hdenominatorEq
  exact hinverse.trans
    (Real.inv_div_div_eq_mul_div
      ‖t‖ (Complex.logarithmicPhaseBProcessScale t)
      (Complex.logarithmicPhaseBProcessWindowRight t m)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ht))
      (Complex.logarithmicPhaseBProcessScale_ne_zero t)
      (ne_of_gt hrightPos))

theorem Complex.logarithmicPhaseBProcessLeftTailBudget_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseBProcessLeftTailBudget t m =
      2 *
        (Complex.logarithmicPhaseBProcessWindowLeft t m *
          Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
  unfold Complex.logarithmicPhaseBProcessLeftTailBudget
  have hgap :=
    Complex.logarithmicPhaseBProcessLeftReciprocalGap_eq_endpoint_mul_scale_div_norm
      t ht hm
  exact
    (congrArg₂ (fun left right : ℝ => left + right) hgap hgap).trans
      (two_mul _).symm

theorem Complex.logarithmicPhaseBProcessRightTailBudget_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseBProcessRightTailBudget t m =
      2 *
        (Complex.logarithmicPhaseBProcessWindowRight t m *
          Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
  unfold Complex.logarithmicPhaseBProcessRightTailBudget
  have hgap :=
    Complex.logarithmicPhaseBProcessRightReciprocalGap_eq_endpoint_mul_scale_div_norm
      t ht hm
  exact
    (congrArg₂ (fun left right : ℝ => left + right) hgap hgap).trans
      (two_mul _).symm

theorem Complex.logarithmicPhaseBProcessWindowLeft_le_center
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseBProcessWindowLeft t m ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  unfold Complex.logarithmicPhaseBProcessWindowLeft
  exact sub_le_self _
    (Complex.logarithmicPhaseBProcessRadius_nonneg t ht hm)

theorem Complex.logarithmicPhaseBProcess_center_le_WindowRight
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤
      Complex.logarithmicPhaseBProcessWindowRight t m := by
  exact
    (Complex.logarithmicPhaseBProcess_center_lt_WindowRight
      t ht hm).le

theorem Complex.logarithmicPhaseBProcessWindowLeft_le_blockRight_of_mem
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    Complex.logarithmicPhaseBProcessWindowLeft t m ≤ (b : ℝ) := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  exact le_trans
    (le_trans
      (Complex.logarithmicPhaseBProcessWindowLeft_le_center
        t ht hmem.2.1)
      (Complex.logarithmicPhaseBProcess_center_le_WindowRight
        t ht hmem.2.1))
    hmem.2.2.2

theorem Complex.logarithmicPhaseBProcessWindowRight_le_blockRight_of_mem
    (t : ℝ) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) := by
  exact
    ((Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm).2.2.2

theorem Complex.logarithmicPhaseBProcessCenter_le_blockRight_of_mem
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ) := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  exact le_trans
    (Complex.logarithmicPhaseBProcess_center_le_WindowRight
      t ht hmem.2.1)
    hmem.2.2.2

theorem Real.mul_div_mono_of_nonneg
    {x y scale divisor : ℝ}
    (hxy : x ≤ y)
    (hscale : 0 ≤ scale)
    (hdivisor : 0 ≤ divisor) :
    x * scale / divisor ≤ y * scale / divisor := by
  have hmul := mul_le_mul_of_nonneg_right hxy hscale
  exact div_le_div_of_nonneg_right hmul hdivisor

theorem Complex.logarithmicPhaseBProcessLeftTailBudget_le_endpoint
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    Complex.logarithmicPhaseBProcessLeftTailBudget t m ≤
      2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  have hendpoint :=
    Complex.logarithmicPhaseBProcessWindowLeft_le_blockRight_of_mem
      t ht hm
  have hinside := Real.mul_div_mono_of_nonneg
    hendpoint
    (Complex.logarithmicPhaseBProcessScale_pos t).le
    (norm_nonneg t)
  have hscaled := mul_le_mul_of_nonneg_left hinside zero_le_two
  exact le_trans
    (le_of_eq
      (Complex.logarithmicPhaseBProcessLeftTailBudget_eq
        t ht hmem.2.1))
    hscaled

theorem Complex.logarithmicPhaseBProcessRightTailBudget_le_endpoint
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    Complex.logarithmicPhaseBProcessRightTailBudget t m ≤
      2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  have hendpoint :=
    Complex.logarithmicPhaseBProcessWindowRight_le_blockRight_of_mem
      t hm
  have hinside := Real.mul_div_mono_of_nonneg
    hendpoint
    (Complex.logarithmicPhaseBProcessScale_pos t).le
    (norm_nonneg t)
  have hscaled := mul_le_mul_of_nonneg_left hinside zero_le_two
  exact le_trans
    (le_of_eq
      (Complex.logarithmicPhaseBProcessRightTailBudget_eq
        t ht hmem.2.1))
    hscaled

theorem Complex.logarithmicPhaseBProcessWindowWidth_le_endpoint
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    Complex.logarithmicPhaseBProcessWindowWidth t m ≤
      2 * ((b : ℝ) / Complex.logarithmicPhaseBProcessScale t) := by
  have hcenter :=
    Complex.logarithmicPhaseBProcessCenter_le_blockRight_of_mem
      t ht hm
  have hdivision :=
    div_le_div_of_nonneg_right hcenter
      (Complex.logarithmicPhaseBProcessScale_pos t).le
  have hscaled := mul_le_mul_of_nonneg_left hdivision zero_le_two
  exact le_trans
    (le_of_eq
      (Complex.logarithmicPhaseBProcessWindowWidth_eq_two_mul_center_div_scale
        t m))
    hscaled

def Complex.logarithmicPhaseBProcessPerModeEndpointMajorant
    (t : ℝ) (b : ℤ) : ℝ :=
  4 / 3 +
    2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) +
      2 * ((b : ℝ) / Complex.logarithmicPhaseBProcessScale t) +
        2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖)

theorem Complex.logarithmicPhaseBProcessStationaryPacketMajorant_le_endpointMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m ≤
      Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b := by
  unfold Complex.logarithmicPhaseBProcessStationaryPacketMajorant
  unfold Complex.logarithmicPhaseBProcessPerModeEndpointMajorant
  exact add_le_add
    (add_le_add
      (add_le_add le_rfl
        (Complex.logarithmicPhaseBProcessLeftTailBudget_le_endpoint
          t ht hm))
      (Complex.logarithmicPhaseBProcessWindowWidth_le_endpoint
        t ht hm))
    (Complex.logarithmicPhaseBProcessRightTailBudget_le_endpoint
      t ht hm)

end

end LFunctions
end Boundary
