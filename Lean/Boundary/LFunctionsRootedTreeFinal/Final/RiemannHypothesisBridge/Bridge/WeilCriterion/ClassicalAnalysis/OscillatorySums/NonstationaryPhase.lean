import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.FrequencyTwist
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!
# Generic nonstationary phase data

This file owns the differential part of one integration-by-parts step for a
real phase.  The interval theorem below will consume continuity and
integrability hypotheses explicitly; no cancellation estimate is hidden in
this layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

/-- Unit-modulus complex oscillation attached to a real phase. -/
def Complex.realPhaseOscillation
    (φ : ℝ → ℝ)
    (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (φ x : ℂ))

/-- Derivative denominator for a real phase oscillation. -/
def Complex.realPhaseDerivativeDenominator
    (φ' : ℝ → ℝ)
    (x : ℝ) : ℂ :=
  Complex.I * (φ' x : ℂ)

/-- Reciprocal coefficient used in nonstationary integration by parts. -/
def Complex.realPhaseIntegrationCoefficient
    (φ' : ℝ → ℝ)
    (x : ℝ) : ℂ :=
  (Complex.realPhaseDerivativeDenominator φ' x)⁻¹

/-- Derivative of the phase oscillation. -/
theorem Complex.hasDerivAt_realPhaseOscillation
    {φ φ' : ℝ → ℝ}
    {x : ℝ}
    (hφ : HasDerivAt φ (φ' x) x) :
    HasDerivAt
      (Complex.realPhaseOscillation φ)
      (Complex.realPhaseOscillation φ x *
        Complex.realPhaseDerivativeDenominator φ' x)
      x := by
  have hφ_complex :
      HasDerivAt
        (fun y : ℝ => (φ y : ℂ))
        ((φ' x : ℂ))
        x :=
    hφ.ofReal_comp
  have hexponent :
      HasDerivAt
        (fun y : ℝ => Complex.I * (φ y : ℂ))
        (Complex.I * (φ' x : ℂ))
        x :=
    hφ_complex.const_mul Complex.I
  have hexponential := hexponent.cexp
  exact hexponential

/-- Derivative of the reciprocal nonstationary coefficient. -/
theorem Complex.hasDerivAt_realPhaseIntegrationCoefficient
    {φ' φ'' : ℝ → ℝ}
    {x : ℝ}
    (hφ' : HasDerivAt φ' (φ'' x) x)
    (hnonzero : Complex.realPhaseDerivativeDenominator φ' x ≠ 0) :
    HasDerivAt
      (Complex.realPhaseIntegrationCoefficient φ')
      (-(Complex.I * (φ'' x : ℂ)) /
        (Complex.realPhaseDerivativeDenominator φ' x) ^ 2)
      x := by
  have hφ'_complex :
      HasDerivAt
        (fun y : ℝ => (φ' y : ℂ))
        ((φ'' x : ℂ))
        x :=
    hφ'.ofReal_comp
  have hdenominator :
      HasDerivAt
        (Complex.realPhaseDerivativeDenominator φ')
        (Complex.I * (φ'' x : ℂ))
        x :=
    hφ'_complex.const_mul Complex.I
  let denominator : ℂ :=
    Complex.realPhaseDerivativeDenominator φ' x
  let derivative : ℂ := Complex.I * (φ'' x : ℂ)
  have hinverse_composed :=
    (hasFDerivAt_inv' hnonzero).comp_hasDerivAt x hdenominator
  have hderivative :
      ((-((ContinuousLinearMap.mulLeftRight ℝ ℂ)
          denominator⁻¹) denominator⁻¹) derivative) =
        -derivative / denominator ^ 2 := by
    calc
      ((-((ContinuousLinearMap.mulLeftRight ℝ ℂ)
          denominator⁻¹) denominator⁻¹) derivative) =
          -(denominator⁻¹ * derivative * denominator⁻¹) :=
        rfl
      _ = -denominator⁻¹ * derivative * denominator⁻¹ := by
        exact
          Eq.trans
            (neg_mul (denominator⁻¹ * derivative) denominator⁻¹).symm
            (congrArg (fun value : ℂ => value * denominator⁻¹)
              (neg_mul denominator⁻¹ derivative).symm)
      _ =
          -derivative * (denominator⁻¹ * denominator⁻¹) := by
        exact
          Eq.trans
            (congrArg (fun value : ℂ => value * denominator⁻¹)
              (Eq.trans
                (neg_mul denominator⁻¹ derivative)
                (congrArg Neg.neg (mul_comm denominator⁻¹ derivative))))
            (Eq.trans
              (congrArg (fun value : ℂ => value * denominator⁻¹)
                (neg_mul derivative denominator⁻¹).symm)
              (mul_assoc (-derivative) denominator⁻¹ denominator⁻¹))
      _ = -derivative * (denominator ^ 2)⁻¹ := by
        exact congrArg (fun value : ℂ => -derivative * value)
          (Eq.trans
            (pow_two denominator⁻¹).symm
            (inv_pow denominator 2))
      _ = -derivative / denominator ^ 2 :=
        (div_eq_mul_inv (-derivative) (denominator ^ 2)).symm
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient φ') value x)
      hderivative
      hinverse_composed

/-- The derivative denominator of a real phase has the norm of its real
derivative. -/
theorem Complex.norm_realPhaseDerivativeDenominator
    (φ' : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.realPhaseDerivativeDenominator φ' x‖ =
      ‖φ' x‖ := by
  have hnorm :
      ‖Complex.I * (φ' x : ℂ)‖ =
        ‖Complex.I‖ * ‖(φ' x : ℂ)‖ :=
    norm_mul Complex.I (φ' x : ℂ)
  exact
    hnorm.trans
      ((congrArg₂ (fun u v : ℝ => u * v)
        Complex.norm_I
        (Complex.norm_real (φ' x))).trans
        (one_mul ‖φ' x‖))

/-- The reciprocal phase coefficient has reciprocal derivative-gap norm. -/
theorem Complex.norm_realPhaseIntegrationCoefficient
    (φ' : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.realPhaseIntegrationCoefficient φ' x‖ =
      (‖φ' x‖)⁻¹ := by
  have hinverse :
      ‖(Complex.realPhaseDerivativeDenominator φ' x)⁻¹‖ =
        ‖Complex.realPhaseDerivativeDenominator φ' x‖⁻¹ :=
    norm_inv (Complex.realPhaseDerivativeDenominator φ' x)
  exact
    hinverse.trans
      (congrArg Inv.inv
      (Complex.norm_realPhaseDerivativeDenominator φ' x))

/-- Exact norm of the universal reciprocal-coefficient derivative numerator
over a squared complex derivative denominator. -/
theorem Complex.norm_neg_I_mul_real_div_sq
    (velocity : ℝ)
    (denominator : ℂ) :
    ‖-(Complex.I * (velocity : ℂ)) / denominator ^ 2‖ =
      |velocity| / ‖denominator‖ ^ 2 := by
  have hdivision :
      ‖-(Complex.I * (velocity : ℂ)) / denominator ^ 2‖ =
        ‖-(Complex.I * (velocity : ℂ))‖ / ‖denominator ^ 2‖ :=
    norm_div
      (-(Complex.I * (velocity : ℂ)))
      (denominator ^ 2)
  have hnegative :
      ‖-(Complex.I * (velocity : ℂ))‖ =
        ‖Complex.I * (velocity : ℂ)‖ :=
    norm_neg (Complex.I * (velocity : ℂ))
  have hproduct :
      ‖Complex.I * (velocity : ℂ)‖ =
        ‖Complex.I‖ * ‖(velocity : ℂ)‖ :=
    norm_mul Complex.I (velocity : ℂ)
  have hnumerator :
      ‖-(Complex.I * (velocity : ℂ))‖ = |velocity| :=
    hnegative.trans
      (hproduct.trans
        ((congrArg₂ (fun left right : ℝ => left * right)
          Complex.norm_I
          (Complex.norm_real velocity)).trans
          (one_mul |velocity|)))
  have hdenominator :
      ‖denominator ^ 2‖ = ‖denominator‖ ^ 2 :=
    norm_pow denominator 2
  exact
    hdivision.trans
      (congrArg₂ (fun numerator divisor : ℝ => numerator / divisor)
        hnumerator hdenominator)

/-- Pointwise cancellation of the reciprocal coefficient with the phase
oscillation derivative. -/
theorem Complex.realPhaseIntegrationCoefficient_mul_deriv
    (φ φ' : ℝ → ℝ)
    (x : ℝ)
    (hnonzero : Complex.realPhaseDerivativeDenominator φ' x ≠ 0) :
    Complex.realPhaseIntegrationCoefficient φ' x *
        (Complex.realPhaseOscillation φ x *
          Complex.realPhaseDerivativeDenominator φ' x) =
      Complex.realPhaseOscillation φ x := by
  let coefficient : ℂ := Complex.realPhaseIntegrationCoefficient φ' x
  let oscillation : ℂ := Complex.realPhaseOscillation φ x
  let denominator : ℂ := Complex.realPhaseDerivativeDenominator φ' x
  have hcancellation : coefficient * denominator = 1 :=
    inv_mul_cancel₀ hnonzero
  have hassociate_left :
      coefficient * (oscillation * denominator) =
        (coefficient * oscillation) * denominator :=
    (mul_assoc coefficient oscillation denominator).symm
  have hcommute : coefficient * oscillation = oscillation * coefficient :=
    mul_comm coefficient oscillation
  have hassociate_right :
      (oscillation * coefficient) * denominator =
        oscillation * (coefficient * denominator) :=
    mul_assoc oscillation coefficient denominator
  exact
    hassociate_left.trans
      ((congrArg (fun value : ℂ => value * denominator) hcommute).trans
        (hassociate_right.trans
          ((congrArg (fun value : ℂ => oscillation * value) hcancellation).trans
            (mul_one oscillation))))

/-- Unit norm of a real phase oscillation. -/
theorem Complex.norm_realPhaseOscillation
    (φ : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.realPhaseOscillation φ x‖ = 1 := by
  have hexponent :
      Complex.I * (φ x : ℂ) = (φ x : ℂ) * Complex.I :=
    mul_comm Complex.I (φ x : ℂ)
  exact
    (congrArg norm
      (congrArg Complex.exp hexponent)).trans
      (Complex.norm_exp_ofReal_mul_I (φ x))

/-- One exact nonstationary integration-by-parts step for a real phase. -/
theorem Complex.intervalIntegral_realPhaseOscillation_eq_boundary_sub_remainder
    (φ φ' : ℝ → ℝ)
    (coefficientDerivative : ℝ → ℂ)
    (oscillationDerivative : ℝ → ℂ)
    (left right : ℝ)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient φ')
          (coefficientDerivative x)
          x)
    (hoscillation :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation φ)
          (oscillationDerivative x)
          x)
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
        Complex.realPhaseDerivativeDenominator φ' x ≠ 0) :
    (∫ x in left..right,
        Complex.realPhaseOscillation φ x) =
      Complex.realPhaseIntegrationCoefficient φ' right *
          Complex.realPhaseOscillation φ right -
        Complex.realPhaseIntegrationCoefficient φ' left *
          Complex.realPhaseOscillation φ left -
        ∫ x in left..right,
          coefficientDerivative x * Complex.realPhaseOscillation φ x := by
  have hcoefficient' :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient φ')
          (coefficientDerivative x)
          x :=
    hcoefficient
  have hoscillation' :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation φ)
          (oscillationDerivative x)
          x :=
    hoscillation
  have hintegration_by_parts :
      (∫ x in left..right,
          Complex.realPhaseIntegrationCoefficient φ' x *
            oscillationDerivative x) =
        Complex.realPhaseIntegrationCoefficient φ' right *
            Complex.realPhaseOscillation φ right -
          Complex.realPhaseIntegrationCoefficient φ' left *
            Complex.realPhaseOscillation φ left -
          ∫ x in left..right,
            coefficientDerivative x * Complex.realPhaseOscillation φ x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hcoefficient'
      hoscillation'
      hcoefficientDerivative_integrable
      hoscillationDerivative_integrable
  have hintegrand :
      Set.EqOn
        (fun x =>
          Complex.realPhaseIntegrationCoefficient φ' x *
            oscillationDerivative x)
        (Complex.realPhaseOscillation φ)
        [[left, right]] := by
    intro x hx
    have hcancel :=
      Complex.realPhaseIntegrationCoefficient_mul_deriv
        φ φ' x (hdenominator x hx)
    exact
      (congrArg
        (fun derivative : ℂ =>
          Complex.realPhaseIntegrationCoefficient φ' x * derivative)
        (hoscillationDerivative_eq x hx)).trans
        hcancel
  have hintegral :
      (∫ x in left..right,
          Complex.realPhaseIntegrationCoefficient φ' x *
            oscillationDerivative x) =
        ∫ x in left..right, Complex.realPhaseOscillation φ x :=
    intervalIntegral.integral_congr hintegrand
  exact hintegral.symm.trans hintegration_by_parts

/-- Norm form of one nonstationary integration-by-parts step. -/
theorem Complex.norm_intervalIntegral_realPhaseOscillation_le_boundary_add_remainder
    (φ φ' : ℝ → ℝ)
    (coefficientDerivative : ℝ → ℂ)
    (oscillationDerivative : ℝ → ℂ)
    (left right : ℝ)
    (hleft_right : left ≤ right)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient φ')
          (coefficientDerivative x)
          x)
    (hoscillation :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation φ)
          (oscillationDerivative x)
          x)
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
        Complex.realPhaseDerivativeDenominator φ' x ≠ 0) :
    ‖∫ x in left..right, Complex.realPhaseOscillation φ x‖ ≤
      ‖Complex.realPhaseIntegrationCoefficient φ' right‖ +
        ‖Complex.realPhaseIntegrationCoefficient φ' left‖ +
        ∫ x in left..right, ‖coefficientDerivative x‖ := by
  have hidentity :=
    Complex.intervalIntegral_realPhaseOscillation_eq_boundary_sub_remainder
      φ φ' coefficientDerivative oscillationDerivative left right
      hcoefficient hoscillation hcoefficientDerivative_integrable
      hoscillationDerivative_integrable hoscillationDerivative_eq hdenominator
  let rightBoundary : ℂ :=
    Complex.realPhaseIntegrationCoefficient φ' right *
      Complex.realPhaseOscillation φ right
  let leftBoundary : ℂ :=
    Complex.realPhaseIntegrationCoefficient φ' left *
      Complex.realPhaseOscillation φ left
  let remainder : ℂ :=
    ∫ x in left..right,
      coefficientDerivative x * Complex.realPhaseOscillation φ x
  have hrewritten :
      (∫ x in left..right, Complex.realPhaseOscillation φ x) =
        rightBoundary - leftBoundary - remainder := by
    exact hidentity
  have htriangle :
      ‖rightBoundary - leftBoundary - remainder‖ ≤
        ‖rightBoundary‖ + ‖leftBoundary‖ + ‖remainder‖ := by
    have hfirst :
        ‖rightBoundary - leftBoundary - remainder‖ ≤
          ‖rightBoundary - leftBoundary‖ + ‖remainder‖ :=
      norm_sub_le (rightBoundary - leftBoundary) remainder
    have hsecond :
        ‖rightBoundary - leftBoundary‖ ≤
          ‖rightBoundary‖ + ‖leftBoundary‖ :=
      norm_sub_le rightBoundary leftBoundary
    have hsum :
        ‖rightBoundary - leftBoundary‖ + ‖remainder‖ ≤
          (‖rightBoundary‖ + ‖leftBoundary‖) + ‖remainder‖ :=
      add_le_add_right hsecond ‖remainder‖
    exact le_trans hfirst hsum
  have hremainder_norm :
      ‖remainder‖ ≤
        ∫ x in left..right, ‖coefficientDerivative x‖ := by
    have hnorm_integral :
        ‖∫ x in left..right,
            coefficientDerivative x * Complex.realPhaseOscillation φ x‖ ≤
          ∫ x in left..right,
            ‖coefficientDerivative x * Complex.realPhaseOscillation φ x‖ :=
      intervalIntegral.norm_integral_le_integral_norm
        hleft_right
        (f := fun x : ℝ =>
          coefficientDerivative x * Complex.realPhaseOscillation φ x)
    have hintegrand :
        Set.EqOn
          (fun x : ℝ =>
            ‖coefficientDerivative x * Complex.realPhaseOscillation φ x‖)
          (fun x : ℝ => ‖coefficientDerivative x‖)
          [[left, right]] := by
      intro x _
      exact
        (norm_mul (coefficientDerivative x)
          (Complex.realPhaseOscillation φ x)).trans
          ((congrArg
            (fun value : ℝ => ‖coefficientDerivative x‖ * value)
            (Complex.norm_realPhaseOscillation φ x)).trans
            (mul_one ‖coefficientDerivative x‖))
    have hintegral :
        (∫ x in left..right,
            ‖coefficientDerivative x * Complex.realPhaseOscillation φ x‖) =
          ∫ x in left..right, ‖coefficientDerivative x‖ :=
      intervalIntegral.integral_congr hintegrand
    exact hnorm_integral.trans (le_of_eq hintegral)
  have hright_norm :
      ‖rightBoundary‖ =
        ‖Complex.realPhaseIntegrationCoefficient φ' right‖ := by
    exact
      (norm_mul
        (Complex.realPhaseIntegrationCoefficient φ' right)
        (Complex.realPhaseOscillation φ right)).trans
        ((congrArg
          (fun value : ℝ =>
            ‖Complex.realPhaseIntegrationCoefficient φ' right‖ * value)
          (Complex.norm_realPhaseOscillation φ right)).trans
          (mul_one ‖Complex.realPhaseIntegrationCoefficient φ' right‖))
  have hleft_norm :
      ‖leftBoundary‖ =
        ‖Complex.realPhaseIntegrationCoefficient φ' left‖ := by
    exact
      (norm_mul
        (Complex.realPhaseIntegrationCoefficient φ' left)
        (Complex.realPhaseOscillation φ left)).trans
        ((congrArg
          (fun value : ℝ =>
            ‖Complex.realPhaseIntegrationCoefficient φ' left‖ * value)
          (Complex.norm_realPhaseOscillation φ left)).trans
          (mul_one ‖Complex.realPhaseIntegrationCoefficient φ' left‖))
  have hcombined :
      ‖rightBoundary - leftBoundary - remainder‖ ≤
        ‖Complex.realPhaseIntegrationCoefficient φ' right‖ +
          ‖Complex.realPhaseIntegrationCoefficient φ' left‖ +
          ∫ x in left..right, ‖coefficientDerivative x‖ := by
    have hboundary :
        ‖rightBoundary‖ + ‖leftBoundary‖ =
          ‖Complex.realPhaseIntegrationCoefficient φ' right‖ +
            ‖Complex.realPhaseIntegrationCoefficient φ' left‖ :=
      congrArg₂ (fun u v : ℝ => u + v) hright_norm hleft_norm
    have hsum_bound :
        (‖rightBoundary‖ + ‖leftBoundary‖) + ‖remainder‖ ≤
          (‖Complex.realPhaseIntegrationCoefficient φ' right‖ +
              ‖Complex.realPhaseIntegrationCoefficient φ' left‖) +
            ∫ x in left..right, ‖coefficientDerivative x‖ :=
      add_le_add (le_of_eq hboundary) hremainder_norm
    exact le_trans htriangle hsum_bound
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          ‖Complex.realPhaseIntegrationCoefficient φ' right‖ +
            ‖Complex.realPhaseIntegrationCoefficient φ' left‖ +
            ∫ x in left..right, ‖coefficientDerivative x‖)
      hrewritten.symm
      hcombined

end

end LFunctions
end Boundary
