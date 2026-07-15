import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.StationaryPhase.FiniteStationaryDecomposition

/-!
# Monotone reciprocal-derivative stationary tails

This file owns the continuous one-sided van der Corput estimate used after a
stationary interval has been removed.  The reciprocal derivative coefficient
is monotone on either side of a simple stationary point.  Consequently its
total variation is an endpoint difference, not an interval length times a
pointwise curvature bound.  In the integration-by-parts estimate the far
endpoint coefficient then cancels against that endpoint difference.

The result is the sharp structural estimate

`norm integral <= 2 * near reciprocal derivative gap`.

No phase-specific witness package is introduced.  The hypotheses expose the
ordinary derivative, coefficient derivative, and scalar reciprocal-gap
function directly, so a specialization proves them from its phase formulas.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

/-- A nonnegative derivative is its own absolute value. -/
theorem Real.abs_eq_self_of_nonnegative
    {x : ℝ}
    (hx : 0 ≤ x) :
    |x| = x :=
  abs_of_nonneg hx

/-- A nonpositive derivative has absolute value equal to its negation. -/
theorem Real.abs_eq_neg_self_of_nonpositive
    {x : ℝ}
    (hx : x ≤ 0) :
    |x| = -x :=
  abs_of_nonpos hx

/-- Endpoint evaluation of the integral of a derivative. -/
theorem Real.intervalIntegral_derivative_eq_endpoint_sub
    (q q' : ℝ → ℝ)
    (left right : ℝ)
    (hderiv :
      ∀ x ∈ [[left, right]], HasDerivAt q (q' x) x)
    (hintegrable : IntervalIntegrable q' volume left right) :
    (∫ x in left..right, q' x) = q right - q left := by
  have hdifferentiable :
      ∀ x ∈ [[left, right]], DifferentiableAt ℝ q x :=
    fun x hx => (hderiv x hx).differentiableAt
  have hderivative :
      Set.EqOn (deriv q) q' [[left, right]] := by
    intro x hx
    exact (hderiv x hx).deriv
  have hderiv_integrable :
      IntervalIntegrable (deriv q) volume left right :=
    hintegrable.congr
      ((ae_restrict_mem measurableSet_uIoc).mono
        (fun x hx => (hderivative (Set.uIoc_subset_uIcc hx)).symm))
  have hfundamental :
      (∫ x in left..right, deriv q x) = q right - q left :=
    intervalIntegral.integral_deriv_eq_sub
      hdifferentiable hderiv_integrable
  have hintegral_congr :
      (∫ x in left..right, deriv q x) =
        ∫ x in left..right, q' x :=
    intervalIntegral.integral_congr hderivative
  exact hintegral_congr.symm.trans hfundamental

/-- The total variation of an increasing differentiable scalar coefficient is
the difference of its endpoint values. -/
theorem Real.intervalIntegral_abs_derivative_eq_endpoint_sub_of_nonneg
    (q q' : ℝ → ℝ)
    (left right : ℝ)
    (hleft_right : left ≤ right)
    (hderiv :
      ∀ x ∈ [[left, right]], HasDerivAt q (q' x) x)
    (hintegrable : IntervalIntegrable q' volume left right)
    (hnonneg : ∀ x ∈ Set.Icc left right, 0 ≤ q' x) :
    (∫ x in left..right, |q' x|) = q right - q left := by
  have huIcc : [[left, right]] = Set.Icc left right :=
    Set.uIcc_of_le hleft_right
  have hintegrands :
      Set.EqOn (fun x : ℝ => |q' x|) q' [[left, right]] := by
    intro x hx
    have hxIcc : x ∈ Set.Icc left right :=
      Eq.subst (motive := fun s : Set ℝ => x ∈ s) huIcc hx
    exact Real.abs_eq_self_of_nonnegative (hnonneg x hxIcc)
  have hintegral :
      (∫ x in left..right, |q' x|) =
        ∫ x in left..right, q' x :=
    intervalIntegral.integral_congr hintegrands
  exact hintegral.trans
    (Real.intervalIntegral_derivative_eq_endpoint_sub
      q q' left right hderiv hintegrable)

/-- The total variation of a decreasing differentiable scalar coefficient is
the reverse endpoint difference. -/
theorem Real.intervalIntegral_abs_derivative_eq_endpoint_sub_of_nonpos
    (q q' : ℝ → ℝ)
    (left right : ℝ)
    (hleft_right : left ≤ right)
    (hderiv :
      ∀ x ∈ [[left, right]], HasDerivAt q (q' x) x)
    (hintegrable : IntervalIntegrable q' volume left right)
    (hnonpos : ∀ x ∈ Set.Icc left right, q' x ≤ 0) :
    (∫ x in left..right, |q' x|) = q left - q right := by
  have huIcc : [[left, right]] = Set.Icc left right :=
    Set.uIcc_of_le hleft_right
  have hintegrands :
      Set.EqOn (fun x : ℝ => |q' x|) (fun x : ℝ => -q' x)
        [[left, right]] := by
    intro x hx
    have hxIcc : x ∈ Set.Icc left right :=
      Eq.subst (motive := fun s : Set ℝ => x ∈ s) huIcc hx
    exact Real.abs_eq_neg_self_of_nonpositive (hnonpos x hxIcc)
  have hintegral_congr :
      (∫ x in left..right, |q' x|) =
        ∫ x in left..right, -q' x :=
    intervalIntegral.integral_congr hintegrands
  have hneg_integral :
      (∫ x in left..right, -q' x) =
        -(∫ x in left..right, q' x) :=
    intervalIntegral.integral_neg (f := q')
  have hderivative_integral :
      (∫ x in left..right, q' x) = q right - q left :=
    Real.intervalIntegral_derivative_eq_endpoint_sub
      q q' left right hderiv hintegrable
  have hneg_endpoint :
      -(q right - q left) = q left - q right :=
    neg_sub (q right) (q left)
  exact
    hintegral_congr.trans
      (hneg_integral.trans
        ((congrArg Neg.neg hderivative_integral).trans hneg_endpoint))

/-- Transport a pointwise norm identity into an interval-integral identity. -/
theorem intervalIntegral_norm_eq_scalar_abs_derivative
    (coefficientDerivative : ℝ → ℂ)
    (q' : ℝ → ℝ)
    (left right : ℝ)
    (hnorm :
      ∀ x ∈ [[left, right]],
        ‖coefficientDerivative x‖ = |q' x|) :
    (∫ x in left..right, ‖coefficientDerivative x‖) =
      ∫ x in left..right, |q' x| := by
  exact intervalIntegral.integral_congr hnorm

/-- Increasing reciprocal-gap variation in endpoint form. -/
theorem intervalIntegral_norm_coefficientDerivative_eq_sub_of_increasing
    (coefficientDerivative : ℝ → ℂ)
    (q q' : ℝ → ℝ)
    (left right : ℝ)
    (hleft_right : left ≤ right)
    (hnorm :
      ∀ x ∈ [[left, right]],
        ‖coefficientDerivative x‖ = |q' x|)
    (hderiv :
      ∀ x ∈ [[left, right]], HasDerivAt q (q' x) x)
    (hintegrable : IntervalIntegrable q' volume left right)
    (hnonneg : ∀ x ∈ Set.Icc left right, 0 ≤ q' x) :
    (∫ x in left..right, ‖coefficientDerivative x‖) =
      q right - q left := by
  have hnorm_integral :=
    intervalIntegral_norm_eq_scalar_abs_derivative
      coefficientDerivative q' left right hnorm
  have habs_integral :=
    Real.intervalIntegral_abs_derivative_eq_endpoint_sub_of_nonneg
      q q' left right hleft_right hderiv hintegrable hnonneg
  exact hnorm_integral.trans habs_integral

/-- Decreasing reciprocal-gap variation in endpoint form. -/
theorem intervalIntegral_norm_coefficientDerivative_eq_sub_of_decreasing
    (coefficientDerivative : ℝ → ℂ)
    (q q' : ℝ → ℝ)
    (left right : ℝ)
    (hleft_right : left ≤ right)
    (hnorm :
      ∀ x ∈ [[left, right]],
        ‖coefficientDerivative x‖ = |q' x|)
    (hderiv :
      ∀ x ∈ [[left, right]], HasDerivAt q (q' x) x)
    (hintegrable : IntervalIntegrable q' volume left right)
    (hnonpos : ∀ x ∈ Set.Icc left right, q' x ≤ 0) :
    (∫ x in left..right, ‖coefficientDerivative x‖) =
      q left - q right := by
  have hnorm_integral :=
    intervalIntegral_norm_eq_scalar_abs_derivative
      coefficientDerivative q' left right hnorm
  have habs_integral :=
    Real.intervalIntegral_abs_derivative_eq_endpoint_sub_of_nonpos
      q q' left right hleft_right hderiv hintegrable hnonpos
  exact hnorm_integral.trans habs_integral

/-- Algebraic cancellation for a decreasing reciprocal coefficient. -/
theorem Real.rightEndpoint_add_leftEndpoint_add_left_sub_right
    (leftValue rightValue : ℝ) :
    rightValue + leftValue + (leftValue - rightValue) =
      leftValue + leftValue := by
  calc
    rightValue + leftValue + (leftValue - rightValue) =
        (rightValue + leftValue + leftValue) - rightValue :=
      (add_sub_assoc (rightValue + leftValue) leftValue rightValue).symm
    _ = ((leftValue + leftValue) + rightValue) - rightValue := by
      exact congrArg (fun value : ℝ => value - rightValue)
        (calc
          rightValue + leftValue + leftValue =
              rightValue + (leftValue + leftValue) :=
            add_assoc rightValue leftValue leftValue
          _ = (leftValue + leftValue) + rightValue :=
            add_comm rightValue (leftValue + leftValue))
    _ = leftValue + leftValue :=
      add_sub_cancel_right (leftValue + leftValue) rightValue

/-- Algebraic cancellation for an increasing reciprocal coefficient. -/
theorem Real.rightEndpoint_add_leftEndpoint_add_right_sub_left
    (leftValue rightValue : ℝ) :
    rightValue + leftValue + (rightValue - leftValue) =
      rightValue + rightValue := by
  calc
    rightValue + leftValue + (rightValue - leftValue) =
        (rightValue + leftValue + rightValue) - leftValue :=
      (add_sub_assoc (rightValue + leftValue) rightValue leftValue).symm
    _ = ((rightValue + rightValue) + leftValue) - leftValue := by
      exact congrArg (fun value : ℝ => value - leftValue)
        (calc
          rightValue + leftValue + rightValue =
              rightValue + (leftValue + rightValue) :=
            add_assoc rightValue leftValue rightValue
          _ = rightValue + (rightValue + leftValue) := by
            exact congrArg (fun value : ℝ => rightValue + value)
              (add_comm leftValue rightValue)
          _ = (rightValue + rightValue) + leftValue :=
            (add_assoc rightValue rightValue leftValue).symm)
    _ = rightValue + rightValue :=
      add_sub_cancel_right (rightValue + rightValue) leftValue

/-- A decreasing reciprocal derivative collapses the nonstationary estimate
to twice the coefficient at the left endpoint. -/
theorem Complex.norm_intervalIntegral_realPhaseOscillation_le_twice_leftCoefficient
    (φ φ' : ℝ → ℝ)
    (coefficientDerivative : ℝ → ℂ)
    (oscillationDerivative : ℝ → ℂ)
    (q q' : ℝ → ℝ)
    (left right : ℝ)
    (hleft_right : left ≤ right)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient φ')
          (coefficientDerivative x) x)
    (hoscillation :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation φ)
          (oscillationDerivative x) x)
    (hcoefficientDerivative_integrable :
      IntervalIntegrable coefficientDerivative volume left right)
    (hoscillationDerivative_integrable :
      IntervalIntegrable oscillationDerivative volume left right)
    (hoscillationDerivative_eq :
      ∀ x ∈ [[left, right]],
        oscillationDerivative x =
          Complex.realPhaseOscillation φ x *
            Complex.realPhaseDerivativeDenominator φ' x)
    (hdenominator :
      ∀ x ∈ [[left, right]],
        Complex.realPhaseDerivativeDenominator φ' x ≠ 0)
    (hq_left :
      q left = ‖Complex.realPhaseIntegrationCoefficient φ' left‖)
    (hq_right :
      q right = ‖Complex.realPhaseIntegrationCoefficient φ' right‖)
    (hnorm_derivative :
      ∀ x ∈ [[left, right]],
        ‖coefficientDerivative x‖ = |q' x|)
    (hq_deriv :
      ∀ x ∈ [[left, right]], HasDerivAt q (q' x) x)
    (hq'_integrable : IntervalIntegrable q' volume left right)
    (hq'_nonpos : ∀ x ∈ Set.Icc left right, q' x ≤ 0) :
    ‖∫ x in left..right, Complex.realPhaseOscillation φ x‖ ≤
      q left + q left := by
  have hstructural :=
    Complex.norm_intervalIntegral_realPhaseOscillation_le_boundary_add_remainder
      φ φ' coefficientDerivative oscillationDerivative left right
      hleft_right hcoefficient hoscillation
      hcoefficientDerivative_integrable hoscillationDerivative_integrable
      hoscillationDerivative_eq hdenominator
  have hvariation :=
    intervalIntegral_norm_coefficientDerivative_eq_sub_of_decreasing
      coefficientDerivative q q' left right hleft_right
      hnorm_derivative hq_deriv hq'_integrable hq'_nonpos
  have hbudget_identity :
      ‖Complex.realPhaseIntegrationCoefficient φ' right‖ +
          ‖Complex.realPhaseIntegrationCoefficient φ' left‖ +
          (∫ x in left..right, ‖coefficientDerivative x‖) =
        q left + q left := by
    calc
      ‖Complex.realPhaseIntegrationCoefficient φ' right‖ +
          ‖Complex.realPhaseIntegrationCoefficient φ' left‖ +
          (∫ x in left..right, ‖coefficientDerivative x‖) =
          q right + q left + (q left - q right) := by
        exact congrArg₂ (fun boundary variation : ℝ => boundary + variation)
          (congrArg₂ (fun u v : ℝ => u + v)
            hq_right.symm hq_left.symm)
          hvariation
      _ = q left + q left :=
        Real.rightEndpoint_add_leftEndpoint_add_left_sub_right
          (q left) (q right)
  exact le_trans hstructural (le_of_eq hbudget_identity)

/-- An increasing reciprocal derivative collapses the nonstationary estimate
to twice the coefficient at the right endpoint. -/
theorem Complex.norm_intervalIntegral_realPhaseOscillation_le_twice_rightCoefficient
    (φ φ' : ℝ → ℝ)
    (coefficientDerivative : ℝ → ℂ)
    (oscillationDerivative : ℝ → ℂ)
    (q q' : ℝ → ℝ)
    (left right : ℝ)
    (hleft_right : left ≤ right)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient φ')
          (coefficientDerivative x) x)
    (hoscillation :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation φ)
          (oscillationDerivative x) x)
    (hcoefficientDerivative_integrable :
      IntervalIntegrable coefficientDerivative volume left right)
    (hoscillationDerivative_integrable :
      IntervalIntegrable oscillationDerivative volume left right)
    (hoscillationDerivative_eq :
      ∀ x ∈ [[left, right]],
        oscillationDerivative x =
          Complex.realPhaseOscillation φ x *
            Complex.realPhaseDerivativeDenominator φ' x)
    (hdenominator :
      ∀ x ∈ [[left, right]],
        Complex.realPhaseDerivativeDenominator φ' x ≠ 0)
    (hq_left :
      q left = ‖Complex.realPhaseIntegrationCoefficient φ' left‖)
    (hq_right :
      q right = ‖Complex.realPhaseIntegrationCoefficient φ' right‖)
    (hnorm_derivative :
      ∀ x ∈ [[left, right]],
        ‖coefficientDerivative x‖ = |q' x|)
    (hq_deriv :
      ∀ x ∈ [[left, right]], HasDerivAt q (q' x) x)
    (hq'_integrable : IntervalIntegrable q' volume left right)
    (hq'_nonneg : ∀ x ∈ Set.Icc left right, 0 ≤ q' x) :
    ‖∫ x in left..right, Complex.realPhaseOscillation φ x‖ ≤
      q right + q right := by
  have hstructural :=
    Complex.norm_intervalIntegral_realPhaseOscillation_le_boundary_add_remainder
      φ φ' coefficientDerivative oscillationDerivative left right
      hleft_right hcoefficient hoscillation
      hcoefficientDerivative_integrable hoscillationDerivative_integrable
      hoscillationDerivative_eq hdenominator
  have hvariation :=
    intervalIntegral_norm_coefficientDerivative_eq_sub_of_increasing
      coefficientDerivative q q' left right hleft_right
      hnorm_derivative hq_deriv hq'_integrable hq'_nonneg
  have hbudget_identity :
      ‖Complex.realPhaseIntegrationCoefficient φ' right‖ +
          ‖Complex.realPhaseIntegrationCoefficient φ' left‖ +
          (∫ x in left..right, ‖coefficientDerivative x‖) =
        q right + q right := by
    calc
      ‖Complex.realPhaseIntegrationCoefficient φ' right‖ +
          ‖Complex.realPhaseIntegrationCoefficient φ' left‖ +
          (∫ x in left..right, ‖coefficientDerivative x‖) =
          q right + q left + (q right - q left) := by
        exact congrArg₂ (fun boundary variation : ℝ => boundary + variation)
          (congrArg₂ (fun u v : ℝ => u + v)
            hq_right.symm hq_left.symm)
          hvariation
      _ = q right + q right :=
        Real.rightEndpoint_add_leftEndpoint_add_right_sub_left
          (q left) (q right)
  exact le_trans hstructural (le_of_eq hbudget_identity)

end

end LFunctions
end Boundary
