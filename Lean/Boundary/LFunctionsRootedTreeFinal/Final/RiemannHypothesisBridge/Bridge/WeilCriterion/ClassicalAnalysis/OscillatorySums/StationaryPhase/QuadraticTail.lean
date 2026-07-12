import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!
# Quadratic oscillatory tails

This file owns the integration-by-parts data for the pure quadratic phase
away from its stationary point at the origin.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval Topology

/-- Pure real quadratic phase. -/
def Real.quadraticOscillatoryPhase
    (frequency x : ℝ) : ℝ :=
  frequency * x ^ 2

/-- Complex exponential of the pure real quadratic phase. -/
def Complex.quadraticOscillation
    (frequency x : ℝ) : ℂ :=
  Complex.exp
    ((Complex.I * (frequency : ℂ)) * (x : ℂ) ^ 2)

/-- Derivative denominator used in integration by parts for a quadratic
oscillation. -/
def Complex.quadraticOscillationDerivativeDenominator
    (frequency x : ℝ) : ℂ :=
  2 * Complex.I * (frequency : ℂ) * (x : ℂ)

/-- The quadratic integration-by-parts denominator is nonzero away from zero
frequency and the stationary point. -/
theorem Complex.quadraticOscillationDerivativeDenominator_ne_zero
    (frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : x ≠ 0) :
    Complex.quadraticOscillationDerivativeDenominator frequency x ≠ 0 := by
  have htwo : (2 : ℂ) ≠ 0 :=
    OfNat.ofNat_ne_zero 2
  have hI : Complex.I ≠ 0 :=
    Complex.I_ne_zero
  have hfrequency_complex : (frequency : ℂ) ≠ 0 := by
    intro hzero
    have hre : frequency = 0 := by
      have hre_complex : ((frequency : ℂ)).re = (0 : ℂ).re :=
        congrArg Complex.re hzero
      exact
        Eq.trans
          (Complex.ofReal_re frequency).symm
          (Eq.trans hre_complex Complex.zero_re)
    exact hfrequency hre
  have hx_complex : (x : ℂ) ≠ 0 := by
    intro hzero
    have hre : x = 0 := by
      have hre_complex : ((x : ℂ)).re = (0 : ℂ).re :=
        congrArg Complex.re hzero
      exact
        Eq.trans
          (Complex.ofReal_re x).symm
          (Eq.trans hre_complex Complex.zero_re)
    exact hx hre
  exact
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero htwo hI)
        hfrequency_complex)
      hx_complex

/-- Reciprocal coefficient used to express the oscillation as a derivative. -/
def Complex.quadraticOscillationIntegrationCoefficient
    (frequency x : ℝ) : ℂ :=
  (Complex.quadraticOscillationDerivativeDenominator frequency x)⁻¹

/-- The integration coefficient times its derivative denominator is one. -/
theorem Complex.quadraticOscillationIntegrationCoefficient_mul_denominator
    (frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : x ≠ 0) :
    Complex.quadraticOscillationIntegrationCoefficient frequency x *
        Complex.quadraticOscillationDerivativeDenominator frequency x = 1 := by
  exact
    inv_mul_cancel₀
      (Complex.quadraticOscillationDerivativeDenominator_ne_zero
        frequency x hfrequency hx)

/-- Pointwise unit norm of a pure quadratic oscillation. -/
theorem Complex.norm_quadraticOscillation
    (frequency x : ℝ) :
    ‖Complex.quadraticOscillation frequency x‖ = 1 := by
  have hsquare : ((x ^ 2 : ℝ) : ℂ) = (x : ℂ) ^ 2 :=
    Complex.ofReal_pow x 2
  have hproduct :
      ((frequency * x ^ 2 : ℝ) : ℂ) =
        (frequency : ℂ) * (x : ℂ) ^ 2 := by
    exact
      (Complex.ofReal_mul frequency (x ^ 2)).trans
        (congrArg
          (fun value : ℂ => (frequency : ℂ) * value)
          hsquare)
  have hexponent :
      (Complex.I * (frequency : ℂ)) * (x : ℂ) ^ 2 =
        ((frequency * x ^ 2 : ℝ) : ℂ) * Complex.I := by
    calc
      (Complex.I * (frequency : ℂ)) * (x : ℂ) ^ 2 =
        Complex.I * ((frequency : ℂ) * (x : ℂ) ^ 2) :=
          mul_assoc Complex.I (frequency : ℂ) ((x : ℂ) ^ 2)
      _ = ((frequency : ℂ) * (x : ℂ) ^ 2) * Complex.I :=
          mul_comm Complex.I ((frequency : ℂ) * (x : ℂ) ^ 2)
      _ = ((frequency * x ^ 2 : ℝ) : ℂ) * Complex.I :=
          congrArg (fun value : ℂ => value * Complex.I) hproduct.symm
  exact
    Eq.subst
      (motive := fun exponent : ℂ => ‖Complex.exp exponent‖ = 1)
      hexponent.symm
      (Complex.norm_exp_ofReal_mul_I (frequency * x ^ 2))

/-- Exact derivative of the pure quadratic oscillation. -/
theorem Complex.hasDerivAt_quadraticOscillation
    (frequency x : ℝ) :
    HasDerivAt
      (Complex.quadraticOscillation frequency)
      (Complex.quadraticOscillation frequency x *
        Complex.quadraticOscillationDerivativeDenominator frequency x)
      x := by
  have hsquare :
      HasDerivAt
        (fun y : ℝ => (y : ℂ) ^ 2)
        (2 * (x : ℂ))
        x := by
    have hraw := (hasDerivAt_pow 2 (x : ℂ)).comp_ofReal
    have hderivative :
        (2 : ℂ) * (x : ℂ) ^ (2 - 1) = 2 * (x : ℂ) := by
      have hindex : (2 - 1 : ℕ) = 1 := rfl
      have hpower : (x : ℂ) ^ (2 - 1) = (x : ℂ) :=
        (congrArg (fun n : ℕ => (x : ℂ) ^ n) hindex).trans
          (pow_one (x : ℂ))
      exact congrArg (fun value : ℂ => (2 : ℂ) * value) hpower
    exact
      Eq.subst
        (motive := fun derivative : ℂ =>
          HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) derivative x)
        hderivative
        hraw
  have hexponent :
      HasDerivAt
        (fun y : ℝ =>
          (Complex.I * (frequency : ℂ)) * (y : ℂ) ^ 2)
        ((Complex.I * (frequency : ℂ)) * (2 * (x : ℂ)))
        x :=
    hsquare.const_mul (Complex.I * (frequency : ℂ))
  have hraw :
      HasDerivAt
        (fun y : ℝ =>
          Complex.exp
            ((Complex.I * (frequency : ℂ)) * (y : ℂ) ^ 2))
        (Complex.exp
            ((Complex.I * (frequency : ℂ)) * (x : ℂ) ^ 2) *
          ((Complex.I * (frequency : ℂ)) * (2 * (x : ℂ))))
        x :=
    hexponent.cexp
  have hdenominator :
      (Complex.I * (frequency : ℂ)) * (2 * (x : ℂ)) =
        2 * Complex.I * (frequency : ℂ) * (x : ℂ) := by
    have hcommute_four :
        (Complex.I * (frequency : ℂ)) * (2 * (x : ℂ)) =
          (Complex.I * 2) * ((frequency : ℂ) * (x : ℂ)) :=
      mul_mul_mul_comm Complex.I (frequency : ℂ) 2 (x : ℂ)
    have hcommute_two : Complex.I * 2 = 2 * Complex.I :=
      mul_comm Complex.I 2
    have hassociate :
        (2 * Complex.I) * ((frequency : ℂ) * (x : ℂ)) =
          2 * Complex.I * (frequency : ℂ) * (x : ℂ) :=
      (mul_assoc (2 * Complex.I) (frequency : ℂ) (x : ℂ)).symm
    exact
      hcommute_four.trans
        ((congrArg
          (fun z : ℂ => z * ((frequency : ℂ) * (x : ℂ)))
          hcommute_two).trans hassociate)
  exact
    Eq.subst
      (motive := fun derivative : ℂ =>
        HasDerivAt
          (Complex.quadraticOscillation frequency)
          (Complex.quadraticOscillation frequency x * derivative)
          x)
      hdenominator
      hraw

/-- Exact derivative of the reciprocal quadratic integration coefficient. -/
theorem Complex.hasDerivAt_quadraticOscillationIntegrationCoefficient
    (frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : x ≠ 0) :
    HasDerivAt
      (Complex.quadraticOscillationIntegrationCoefficient frequency)
      (-(2 * Complex.I * (frequency : ℂ)) /
        (Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2)
      x := by
  let constant : ℂ := 2 * Complex.I * (frequency : ℂ)
  have hcomplexLinear :
      HasDerivAt
        (fun z : ℂ => constant * z)
        constant
        (x : ℂ) := by
    have hraw :
        HasDerivAt
          (fun z : ℂ => constant * z)
          (constant * 1)
          (x : ℂ) :=
      (hasDerivAt_id (x : ℂ)).const_mul constant
    exact
      Eq.subst
        (motive := fun derivative : ℂ =>
          HasDerivAt
            (fun z : ℂ => constant * z)
            derivative (x : ℂ))
        (mul_one constant)
        hraw
  have hcomplexInverse :
      HasDerivAt
        (fun z : ℂ => (constant * z)⁻¹)
        (-constant / (constant * (x : ℂ)) ^ 2)
        (x : ℂ) :=
    hcomplexLinear.inv
      (Complex.quadraticOscillationDerivativeDenominator_ne_zero
        frequency x hfrequency hx)
  have hinverse :
      HasDerivAt
        (fun y : ℝ =>
          (Complex.quadraticOscillationDerivativeDenominator frequency y)⁻¹)
        (-constant /
          (Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2)
        x :=
    hcomplexInverse.comp_ofReal
  exact hinverse

/-- Pointwise cancellation that turns the integration-by-parts left-hand
side back into the quadratic oscillation. -/
theorem Complex.quadraticOscillationIntegrationCoefficient_mul_deriv
    (frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : x ≠ 0) :
    Complex.quadraticOscillationIntegrationCoefficient frequency x *
        (Complex.quadraticOscillation frequency x *
          Complex.quadraticOscillationDerivativeDenominator frequency x) =
      Complex.quadraticOscillation frequency x := by
  let coefficient : ℂ :=
    Complex.quadraticOscillationIntegrationCoefficient frequency x
  let oscillation : ℂ :=
    Complex.quadraticOscillation frequency x
  let denominator : ℂ :=
    Complex.quadraticOscillationDerivativeDenominator frequency x
  have hcancellation : coefficient * denominator = 1 :=
    Complex.quadraticOscillationIntegrationCoefficient_mul_denominator
      frequency x hfrequency hx
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
      ((congrArg (fun z : ℂ => z * denominator) hcommute).trans
        (hassociate_right.trans
          ((congrArg (fun z : ℂ => oscillation * z) hcancellation).trans
            (mul_one oscillation))))

/-- The derivative occurring on the remainder side of quadratic integration
by parts. -/
def Complex.quadraticOscillationIntegrationCoefficientDerivative
    (frequency x : ℝ) : ℂ :=
  -(2 * Complex.I * (frequency : ℂ)) /
    (Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2

/-- The derivative occurring on the oscillatory side of quadratic integration
by parts. -/
def Complex.quadraticOscillationDerivative
    (frequency x : ℝ) : ℂ :=
  Complex.quadraticOscillation frequency x *
    Complex.quadraticOscillationDerivativeDenominator frequency x

/-- The quadratic derivative denominator varies continuously. -/
theorem Complex.continuous_quadraticOscillationDerivativeDenominator
    (frequency : ℝ) :
    Continuous
      (Complex.quadraticOscillationDerivativeDenominator frequency) := by
  have hconstant :
      Continuous (fun _ : ℝ =>
        2 * Complex.I * (frequency : ℂ)) :=
    continuous_const
  have hcoordinate : Continuous (fun x : ℝ => (x : ℂ)) :=
    Complex.continuous_ofReal
  exact hconstant.mul hcoordinate

/-- Pure quadratic oscillation varies continuously. -/
theorem Complex.continuous_quadraticOscillation
    (frequency : ℝ) :
    Continuous (Complex.quadraticOscillation frequency) := by
  exact
    continuous_iff_continuousAt.mpr
      (fun x =>
        (Complex.hasDerivAt_quadraticOscillation frequency x).continuousAt)

/-- The quadratic oscillation derivative varies continuously. -/
theorem Complex.continuous_quadraticOscillationDerivative
    (frequency : ℝ) :
    Continuous (Complex.quadraticOscillationDerivative frequency) := by
  exact
    (Complex.continuous_quadraticOscillation frequency).mul
      (Complex.continuous_quadraticOscillationDerivativeDenominator frequency)

/-- The reciprocal coefficient varies continuously on every interval that
does not meet the stationary point. -/
theorem Complex.continuousOn_quadraticOscillationIntegrationCoefficient
    (frequency : ℝ)
    (hfrequency : frequency ≠ 0)
    (set : Set ℝ)
    (hset : ∀ x ∈ set, x ≠ 0) :
    ContinuousOn
      (Complex.quadraticOscillationIntegrationCoefficient frequency)
      set := by
  have hdenominator :
      ContinuousOn
        (Complex.quadraticOscillationDerivativeDenominator frequency)
        set :=
    (Complex.continuous_quadraticOscillationDerivativeDenominator frequency).continuousOn
  exact
    hdenominator.inv₀
      (fun x hx =>
        Complex.quadraticOscillationDerivativeDenominator_ne_zero
          frequency x hfrequency (hset x hx))

/-- The reciprocal-coefficient derivative varies continuously on every
interval that does not meet the stationary point. -/
theorem Complex.continuousOn_quadraticOscillationIntegrationCoefficientDerivative
    (frequency : ℝ)
    (hfrequency : frequency ≠ 0)
    (set : Set ℝ)
    (hset : ∀ x ∈ set, x ≠ 0) :
    ContinuousOn
      (Complex.quadraticOscillationIntegrationCoefficientDerivative frequency)
      set := by
  have hnumerator :
      ContinuousOn
        (fun _ : ℝ => -(2 * Complex.I * (frequency : ℂ)))
        set :=
    continuousOn_const
  have hdenominator :
      ContinuousOn
        (fun x : ℝ =>
          (Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2)
        set :=
    (Complex.continuous_quadraticOscillationDerivativeDenominator frequency).continuousOn.pow 2
  have hdenominator_ne :
      ∀ x ∈ set,
        (Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2 ≠ 0 :=
    fun x hx =>
      pow_ne_zero 2
        (Complex.quadraticOscillationDerivativeDenominator_ne_zero
          frequency x hfrequency (hset x hx))
  exact hnumerator.div hdenominator hdenominator_ne

/-- Every point of a positive closed interval is different from the
stationary point. -/
theorem Real.ne_zero_of_mem_Icc_of_pos_left
    {left right x : ℝ}
    (hleft : 0 < left)
    (hx : x ∈ Set.Icc left right) :
    x ≠ 0 := by
  have hx_pos : 0 < x :=
    lt_of_lt_of_le hleft hx.1
  exact ne_of_gt hx_pos

/-- Exact integration by parts for a pure quadratic oscillation on a positive
closed interval.  This is the finite tail identity used by stationary phase. -/
theorem Complex.intervalIntegral_quadraticOscillation_eq_boundary_sub_remainder
    (frequency left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    (∫ x in left..right,
        Complex.quadraticOscillation frequency x) =
      Complex.quadraticOscillationIntegrationCoefficient frequency right *
          Complex.quadraticOscillation frequency right -
        Complex.quadraticOscillationIntegrationCoefficient frequency left *
          Complex.quadraticOscillation frequency left -
        ∫ x in left..right,
          Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x *
            Complex.quadraticOscillation frequency x := by
  let coefficient : ℝ → ℂ :=
    Complex.quadraticOscillationIntegrationCoefficient frequency
  let oscillation : ℝ → ℂ :=
    Complex.quadraticOscillation frequency
  let coefficientDerivative : ℝ → ℂ :=
    Complex.quadraticOscillationIntegrationCoefficientDerivative frequency
  let oscillationDerivative : ℝ → ℂ :=
    Complex.quadraticOscillationDerivative frequency
  have hinterval : [[left, right]] = Set.Icc left right :=
    Set.uIcc_of_le hleft_right
  have hnonzero :
      ∀ x ∈ [[left, right]], x ≠ 0 := by
    intro x hx
    have hx_Icc : x ∈ Set.Icc left right :=
      hinterval ▸ hx
    exact Real.ne_zero_of_mem_Icc_of_pos_left hleft hx_Icc
  have hcoefficient_derivative :
      ∀ x ∈ [[left, right]],
        HasDerivAt coefficient (coefficientDerivative x) x := by
    intro x hx
    exact
      Complex.hasDerivAt_quadraticOscillationIntegrationCoefficient
        frequency x hfrequency (hnonzero x hx)
  have hoscillation_derivative :
      ∀ x ∈ [[left, right]],
        HasDerivAt oscillation (oscillationDerivative x) x := by
    intro x _
    exact Complex.hasDerivAt_quadraticOscillation frequency x
  have hcoefficientDerivative_integrable :
      IntervalIntegrable coefficientDerivative volume left right := by
    have hcontinuous_Icc :
        ContinuousOn coefficientDerivative (Set.Icc left right) :=
      Complex.continuousOn_quadraticOscillationIntegrationCoefficientDerivative
        frequency hfrequency (Set.Icc left right)
        (fun x hx =>
          Real.ne_zero_of_mem_Icc_of_pos_left hleft hx)
    exact hcontinuous_Icc.intervalIntegrable_of_Icc hleft_right
  have hoscillationDerivative_integrable :
      IntervalIntegrable oscillationDerivative volume left right :=
    (Complex.continuous_quadraticOscillationDerivative frequency).continuousOn.intervalIntegrable
  have hintegration_by_parts :
      (∫ x in left..right, coefficient x * oscillationDerivative x) =
        coefficient right * oscillation right -
          coefficient left * oscillation left -
          ∫ x in left..right, coefficientDerivative x * oscillation x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hcoefficient_derivative
      hoscillation_derivative
      hcoefficientDerivative_integrable
      hoscillationDerivative_integrable
  have hintegrand :
      Set.EqOn
        (fun x => coefficient x * oscillationDerivative x)
        oscillation
        [[left, right]] := by
    intro x hx
    exact
      Complex.quadraticOscillationIntegrationCoefficient_mul_deriv
        frequency x hfrequency (hnonzero x hx)
  have hintegral :
      (∫ x in left..right, coefficient x * oscillationDerivative x) =
        ∫ x in left..right, oscillation x :=
    intervalIntegral.integral_congr hintegrand
  exact
    Eq.trans hintegral.symm hintegration_by_parts

/-- Norm estimate obtained directly from the finite quadratic tail identity.
The two endpoint terms and the coefficient-variation remainder remain visible
so later stationary-phase arguments can estimate them at their natural owner
levels. -/
theorem Complex.norm_intervalIntegral_quadraticOscillation_le_boundary_add_remainder
    (frequency left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
        Complex.quadraticOscillation frequency x‖ ≤
      ‖Complex.quadraticOscillationIntegrationCoefficient frequency right‖ +
        ‖Complex.quadraticOscillationIntegrationCoefficient frequency left‖ +
        ∫ x in left..right,
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x‖ := by
  let rightBoundary : ℂ :=
    Complex.quadraticOscillationIntegrationCoefficient frequency right *
      Complex.quadraticOscillation frequency right
  let leftBoundary : ℂ :=
    Complex.quadraticOscillationIntegrationCoefficient frequency left *
      Complex.quadraticOscillation frequency left
  let remainder : ℂ :=
    ∫ x in left..right,
      Complex.quadraticOscillationIntegrationCoefficientDerivative frequency x *
        Complex.quadraticOscillation frequency x
  have hidentity :
      (∫ x in left..right,
          Complex.quadraticOscillation frequency x) =
        rightBoundary - leftBoundary - remainder :=
    Complex.intervalIntegral_quadraticOscillation_eq_boundary_sub_remainder
      frequency left right hfrequency hleft hleft_right
  have hfirst_triangle :
      ‖rightBoundary - leftBoundary - remainder‖ ≤
        ‖rightBoundary - leftBoundary‖ + ‖remainder‖ :=
    norm_sub_le (rightBoundary - leftBoundary) remainder
  have hboundary_triangle :
      ‖rightBoundary - leftBoundary‖ ≤
        ‖rightBoundary‖ + ‖leftBoundary‖ :=
    norm_sub_le rightBoundary leftBoundary
  have hremainder_triangle :
      ‖remainder‖ ≤
        ∫ x in left..right,
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x *
            Complex.quadraticOscillation frequency x‖ :=
    intervalIntegral.norm_integral_le_integral_norm hleft_right
  have hright_norm :
      ‖rightBoundary‖ =
        ‖Complex.quadraticOscillationIntegrationCoefficient frequency right‖ := by
    have hproduct :
        ‖rightBoundary‖ =
          ‖Complex.quadraticOscillationIntegrationCoefficient frequency right‖ *
            ‖Complex.quadraticOscillation frequency right‖ :=
      norm_mul
        (Complex.quadraticOscillationIntegrationCoefficient frequency right)
        (Complex.quadraticOscillation frequency right)
    exact
      hproduct.trans
        ((congrArg
          (fun value : ℝ =>
            ‖Complex.quadraticOscillationIntegrationCoefficient frequency right‖ *
              value)
          (Complex.norm_quadraticOscillation frequency right)).trans
          (mul_one
            ‖Complex.quadraticOscillationIntegrationCoefficient frequency right‖))
  have hleft_norm :
      ‖leftBoundary‖ =
        ‖Complex.quadraticOscillationIntegrationCoefficient frequency left‖ := by
    have hproduct :
        ‖leftBoundary‖ =
          ‖Complex.quadraticOscillationIntegrationCoefficient frequency left‖ *
            ‖Complex.quadraticOscillation frequency left‖ :=
      norm_mul
        (Complex.quadraticOscillationIntegrationCoefficient frequency left)
        (Complex.quadraticOscillation frequency left)
    exact
      hproduct.trans
        ((congrArg
          (fun value : ℝ =>
            ‖Complex.quadraticOscillationIntegrationCoefficient frequency left‖ *
              value)
          (Complex.norm_quadraticOscillation frequency left)).trans
          (mul_one
            ‖Complex.quadraticOscillationIntegrationCoefficient frequency left‖))
  have hintegrand_norm :
      Set.EqOn
        (fun x =>
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x *
            Complex.quadraticOscillation frequency x‖)
        (fun x =>
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x‖)
        [[left, right]] := by
    intro x _
    have hproduct :
        ‖Complex.quadraticOscillationIntegrationCoefficientDerivative frequency x *
            Complex.quadraticOscillation frequency x‖ =
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative frequency x‖ *
            ‖Complex.quadraticOscillation frequency x‖ :=
      norm_mul
        (Complex.quadraticOscillationIntegrationCoefficientDerivative frequency x)
        (Complex.quadraticOscillation frequency x)
    exact
      hproduct.trans
        ((congrArg
          (fun value : ℝ =>
            ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
                frequency x‖ * value)
          (Complex.norm_quadraticOscillation frequency x)).trans
          (mul_one
            ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
                frequency x‖))
  have hintegral_norm :
      (∫ x in left..right,
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x *
            Complex.quadraticOscillation frequency x‖) =
        ∫ x in left..right,
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x‖ :=
    intervalIntegral.integral_congr hintegrand_norm
  have hcombined :
      ‖rightBoundary - leftBoundary - remainder‖ ≤
        (‖rightBoundary‖ + ‖leftBoundary‖) +
          ∫ x in left..right,
            ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
                frequency x‖ :=
    le_trans hfirst_triangle
      (add_le_add hboundary_triangle
        (le_trans hremainder_triangle (le_of_eq hintegral_norm)))
  have hnormalized :
      (‖rightBoundary‖ + ‖leftBoundary‖) +
          ∫ x in left..right,
            ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
                frequency x‖ =
        ‖Complex.quadraticOscillationIntegrationCoefficient frequency right‖ +
          ‖Complex.quadraticOscillationIntegrationCoefficient frequency left‖ +
          ∫ x in left..right,
            ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
                frequency x‖ :=
    congrArg
      (fun boundaryNorm : ℝ =>
        boundaryNorm +
          ∫ x in left..right,
            ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
                frequency x‖)
      (congrArg₂ (fun x y : ℝ => x + y) hright_norm hleft_norm)
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          ‖Complex.quadraticOscillationIntegrationCoefficient frequency right‖ +
            ‖Complex.quadraticOscillationIntegrationCoefficient frequency left‖ +
            ∫ x in left..right,
              ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
                  frequency x‖)
      hidentity.symm
      (le_trans hcombined (le_of_eq hnormalized))

/-- Exact norm of the derivative denominator for the pure quadratic phase. -/
theorem Complex.norm_quadraticOscillationDerivativeDenominator
    (frequency x : ℝ) :
    ‖Complex.quadraticOscillationDerivativeDenominator frequency x‖ =
      2 * ‖frequency‖ * ‖x‖ := by
  have houter :
      ‖2 * Complex.I * (frequency : ℂ) * (x : ℂ)‖ =
        ‖2 * Complex.I * (frequency : ℂ)‖ * ‖(x : ℂ)‖ :=
    norm_mul (2 * Complex.I * (frequency : ℂ)) (x : ℂ)
  have hmiddle :
      ‖2 * Complex.I * (frequency : ℂ)‖ =
        ‖2 * Complex.I‖ * ‖(frequency : ℂ)‖ :=
    norm_mul (2 * Complex.I) (frequency : ℂ)
  have hinner :
      ‖2 * Complex.I‖ = ‖(2 : ℂ)‖ * ‖Complex.I‖ :=
    norm_mul (2 : ℂ) Complex.I
  have htwo : ‖(2 : ℂ)‖ = 2 :=
    Complex.norm_ofNat 2
  have hI : ‖Complex.I‖ = 1 :=
    Complex.norm_I
  have hfrequency : ‖(frequency : ℂ)‖ = ‖frequency‖ :=
    Complex.norm_real frequency
  have hx : ‖(x : ℂ)‖ = ‖x‖ :=
    Complex.norm_real x
  have hinner_normalized : ‖2 * Complex.I‖ = 2 :=
    hinner.trans
      ((congrArg₂ (fun u v : ℝ => u * v) htwo hI).trans
        (mul_one 2))
  have hmiddle_normalized :
      ‖2 * Complex.I * (frequency : ℂ)‖ = 2 * ‖frequency‖ :=
    hmiddle.trans
      (congrArg₂ (fun u v : ℝ => u * v)
        hinner_normalized hfrequency)
  exact
    houter.trans
      (congrArg₂ (fun u v : ℝ => u * v)
        hmiddle_normalized hx)

/-- Exact norm of the reciprocal coefficient used in quadratic integration
by parts. -/
theorem Complex.norm_quadraticOscillationIntegrationCoefficient
    (frequency x : ℝ) :
    ‖Complex.quadraticOscillationIntegrationCoefficient frequency x‖ =
      (2 * ‖frequency‖ * ‖x‖)⁻¹ := by
  have hinverse :
      ‖(Complex.quadraticOscillationDerivativeDenominator frequency x)⁻¹‖ =
        ‖Complex.quadraticOscillationDerivativeDenominator frequency x‖⁻¹ :=
    norm_inv
      (Complex.quadraticOscillationDerivativeDenominator frequency x)
  exact
    hinverse.trans
      (congrArg Inv.inv
        (Complex.norm_quadraticOscillationDerivativeDenominator frequency x))

/-- Exact norm of the reciprocal-coefficient derivative. -/
theorem Complex.norm_quadraticOscillationIntegrationCoefficientDerivative
    (frequency x : ℝ) :
    ‖Complex.quadraticOscillationIntegrationCoefficientDerivative frequency x‖ =
      (2 * ‖frequency‖) /
        (2 * ‖frequency‖ * ‖x‖) ^ 2 := by
  have hdivision :
      ‖-(2 * Complex.I * (frequency : ℂ)) /
          (Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2‖ =
        ‖-(2 * Complex.I * (frequency : ℂ))‖ /
          ‖(Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2‖ :=
    norm_div
      (-(2 * Complex.I * (frequency : ℂ)))
      ((Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2)
  have hnumerator_neg :
      ‖-(2 * Complex.I * (frequency : ℂ))‖ =
        ‖2 * Complex.I * (frequency : ℂ)‖ :=
    norm_neg (2 * Complex.I * (frequency : ℂ))
  have hnumerator :
      ‖2 * Complex.I * (frequency : ℂ)‖ = 2 * ‖frequency‖ := by
    have hproduct :
        ‖2 * Complex.I * (frequency : ℂ)‖ =
          ‖2 * Complex.I‖ * ‖(frequency : ℂ)‖ :=
      norm_mul (2 * Complex.I) (frequency : ℂ)
    have htwoI : ‖2 * Complex.I‖ = 2 := by
      have hraw : ‖2 * Complex.I‖ = ‖(2 : ℂ)‖ * ‖Complex.I‖ :=
        norm_mul (2 : ℂ) Complex.I
      exact
        hraw.trans
          ((congrArg₂ (fun u v : ℝ => u * v)
            (Complex.norm_ofNat 2) Complex.norm_I).trans
            (mul_one 2))
    exact
      hproduct.trans
        (congrArg₂ (fun u v : ℝ => u * v)
          htwoI (Complex.norm_real frequency))
  have hdenominator_pow :
      ‖(Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2‖ =
        ‖Complex.quadraticOscillationDerivativeDenominator frequency x‖ ^ 2 :=
    norm_pow
      (Complex.quadraticOscillationDerivativeDenominator frequency x)
      2
  have hdenominator :
      ‖(Complex.quadraticOscillationDerivativeDenominator frequency x) ^ 2‖ =
        (2 * ‖frequency‖ * ‖x‖) ^ 2 :=
    hdenominator_pow.trans
      (congrArg (fun value : ℝ => value ^ 2)
        (Complex.norm_quadraticOscillationDerivativeDenominator frequency x))
  exact
    hdivision.trans
      (congrArg₂ (fun u v : ℝ => u / v)
        (hnumerator_neg.trans hnumerator)
        hdenominator)

/-- The exact inverse-square integral on a positive interval, retained in
integer-power normal form.  Subsequent estimates can normalize the endpoint
expression independently of the integration argument. -/
theorem Real.intervalIntegral_zpow_neg_two
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    (∫ x in left..right, x ^ (-2 : ℤ)) =
      (right ^ ((-2 : ℤ) + 1) - left ^ ((-2 : ℤ) + 1)) /
        (((-2 : ℤ) + 1 : ℤ) : ℝ) := by
  have hright : 0 < right :=
    lt_of_lt_of_le hleft hleft_right
  have hminus_two_ne_minus_one : (-2 : ℤ) ≠ -1 := by
    intro hequal
    have hpositive_equal : (2 : ℤ) = 1 :=
      neg_inj.mp hequal
    exact (OfNat.ofNat_ne_one 2) hpositive_equal
  have hzero_not_mem : (0 : ℝ) ∉ [[left, right]] :=
    Set.not_mem_uIcc_of_lt hleft hright
  have hraw :=
    integral_zpow
      (Or.inr
        (And.intro hminus_two_ne_minus_one hzero_not_mem))
  have hcastDenominator :
      ((((-2 : ℤ) + 1 : ℤ) : ℝ)) =
        (((-2 : ℤ) : ℝ) + 1) :=
    (Int.cast_add (-2) 1).trans
      (congrArg
        (fun value : ℝ => ((-2 : ℤ) : ℝ) + value)
        (Int.cast_one : ((1 : ℤ) : ℝ) = 1))
  exact
    Eq.subst
      (motive := fun denominator : ℝ =>
        (∫ x in left..right, x ^ (-2 : ℤ)) =
          (right ^ ((-2 : ℤ) + 1) - left ^ ((-2 : ℤ) + 1)) /
            denominator)
      hcastDenominator.symm
      hraw

/-- Positive-interval inverse-square integral in endpoint form. -/
theorem Real.intervalIntegral_inv_square
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    (∫ x in left..right, x ^ (-2 : ℤ)) = left⁻¹ - right⁻¹ := by
  have hraw :=
    Real.intervalIntegral_zpow_neg_two left right hleft hleft_right
  have hindex : ((-2 : ℤ) + 1) = -1 :=
    rfl
  have hright_power : right ^ ((-2 : ℤ) + 1) = right⁻¹ :=
    (congrArg (fun exponent : ℤ => right ^ exponent) hindex).trans
      (zpow_neg_one right)
  have hleft_power : left ^ ((-2 : ℤ) + 1) = left⁻¹ :=
    (congrArg (fun exponent : ℤ => left ^ exponent) hindex).trans
      (zpow_neg_one left)
  have hdenominator : ((((-2 : ℤ) + 1 : ℤ) : ℝ)) = -1 :=
    (congrArg (fun integer : ℤ => (integer : ℝ)) hindex).trans
      ((Int.cast_neg 1).trans
        (congrArg Neg.neg
          (Int.cast_one : ((1 : ℤ) : ℝ) = 1)))
  have hquotient :
      (right⁻¹ - left⁻¹) / (-1 : ℝ) = left⁻¹ - right⁻¹ := by
    have hdiv_neg :
        (right⁻¹ - left⁻¹) / (-1 : ℝ) =
          -((right⁻¹ - left⁻¹) / (1 : ℝ)) :=
      div_neg (right⁻¹ - left⁻¹)
    have hdiv_one :
        (right⁻¹ - left⁻¹) / (1 : ℝ) = right⁻¹ - left⁻¹ :=
      div_one (right⁻¹ - left⁻¹)
    exact
      hdiv_neg.trans
        ((congrArg Neg.neg hdiv_one).trans
          (neg_sub right⁻¹ left⁻¹))
  have hnormalized_rhs :
      (right ^ ((-2 : ℤ) + 1) - left ^ ((-2 : ℤ) + 1)) /
          ((((-2 : ℤ) + 1 : ℤ) : ℝ)) =
        left⁻¹ - right⁻¹ :=
    (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
      (congrArg₂ (fun u v : ℝ => u - v) hright_power hleft_power)
      hdenominator).trans hquotient
  exact hraw.trans hnormalized_rhs

/-- Cancellation identity behind the inverse-square quadratic tail
majorant. -/
theorem Real.div_mul_square_eq_inv_mul_square_inv
    (scale x : ℝ)
    (hscale : scale ≠ 0) :
    scale / (scale * x) ^ 2 = scale⁻¹ * (x ^ 2)⁻¹ := by
  have hdenominator :
      (scale * x) ^ 2 = scale * (scale * x ^ 2) := by
    calc
      (scale * x) ^ 2 = (scale * x) * (scale * x) :=
        pow_two (scale * x)
      _ = scale * (x * (scale * x)) :=
        mul_assoc scale x (scale * x)
      _ = scale * (scale * (x * x)) := by
        have hinterior : x * (scale * x) = scale * (x * x) := by
          calc
            x * (scale * x) = (x * scale) * x :=
              (mul_assoc x scale x).symm
            _ = (scale * x) * x :=
              congrArg (fun value : ℝ => value * x) (mul_comm x scale)
            _ = scale * (x * x) :=
              mul_assoc scale x x
        exact congrArg (fun value : ℝ => scale * value) hinterior
      _ = scale * (scale * x ^ 2) :=
        congrArg
          (fun value : ℝ => scale * (scale * value))
          (pow_two x).symm
  have hcancel :
      scale / (scale * (scale * x ^ 2)) = (scale * x ^ 2)⁻¹ :=
    div_mul_cancel_left₀ hscale (scale * x ^ 2)
  have hinverse_product :
      (scale * x ^ 2)⁻¹ = (x ^ 2)⁻¹ * scale⁻¹ :=
    mul_inv_rev scale (x ^ 2)
  have hcommute :
      (x ^ 2)⁻¹ * scale⁻¹ = scale⁻¹ * (x ^ 2)⁻¹ :=
    mul_comm (x ^ 2)⁻¹ scale⁻¹
  exact
    (congrArg (fun denominator : ℝ => scale / denominator) hdenominator).trans
      (hcancel.trans (hinverse_product.trans hcommute))

/-- On the positive half-line the coefficient-variation norm is exactly a
constant multiple of the inverse-square density. -/
theorem Complex.norm_quadraticOscillationIntegrationCoefficientDerivative_eq_invSquare
    (frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : 0 < x) :
    ‖Complex.quadraticOscillationIntegrationCoefficientDerivative frequency x‖ =
      (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹ := by
  let scale : ℝ := 2 * ‖frequency‖
  have hfrequency_norm_pos : 0 < ‖frequency‖ :=
    norm_pos_iff.mpr hfrequency
  have hscale_pos : 0 < scale :=
    mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ 1)) hfrequency_norm_pos
  have hscale_ne : scale ≠ 0 :=
    ne_of_gt hscale_pos
  have hx_norm : ‖x‖ = x :=
    Real.norm_of_nonneg (le_of_lt hx)
  have hraw :
      ‖Complex.quadraticOscillationIntegrationCoefficientDerivative frequency x‖ =
        scale / (scale * x) ^ 2 :=
    (Complex.norm_quadraticOscillationIntegrationCoefficientDerivative
      frequency x).trans
      (congrArg
        (fun coordinate : ℝ => scale / (scale * coordinate) ^ 2)
        hx_norm)
  exact
    hraw.trans
      (Real.div_mul_square_eq_inv_mul_square_inv scale x hscale_ne)

/-- Integer exponent `-2` is the inverse of the ordinary square. -/
theorem Real.zpow_neg_two_eq_square_inv
    (x : ℝ) :
    x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := by
  have hnegative : (-(2 : ℤ)) = (-2 : ℤ) :=
    rfl
  have hneg_power :
      x ^ (-(2 : ℤ)) = (x ^ (2 : ℤ))⁻¹ :=
    zpow_neg x (2 : ℤ)
  have hnatural_power : x ^ (2 : ℤ) = x ^ (2 : ℕ) :=
    zpow_natCast x 2
  exact
    Eq.subst
      (motive := fun exponent : ℤ => x ^ exponent = (x ^ 2)⁻¹)
      hnegative
      (hneg_power.trans (congrArg Inv.inv hnatural_power))

/-- Integral of the ordinary inverse-square density on a positive interval. -/
theorem Real.intervalIntegral_square_inv
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    (∫ x in left..right, (x ^ 2)⁻¹) = left⁻¹ - right⁻¹ := by
  have hintegrands :
      Set.EqOn
        (fun x : ℝ => (x ^ 2)⁻¹)
        (fun x : ℝ => x ^ (-2 : ℤ))
        [[left, right]] := by
    intro x _
    exact (Real.zpow_neg_two_eq_square_inv x).symm
  have hintegrals :
      (∫ x in left..right, (x ^ 2)⁻¹) =
        ∫ x in left..right, x ^ (-2 : ℤ) :=
    intervalIntegral.integral_congr hintegrands
  exact
    hintegrals.trans
      (Real.intervalIntegral_inv_square left right hleft hleft_right)

/-- Exact integral of the quadratic coefficient-variation norm on a positive
interval. -/
theorem Complex.intervalIntegral_norm_quadraticOscillationIntegrationCoefficientDerivative
    (frequency left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    (∫ x in left..right,
        ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
            frequency x‖) =
      (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹) := by
  have hintegrands :
      Set.EqOn
        (fun x : ℝ =>
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x‖)
        (fun x : ℝ => (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹)
        [[left, right]] := by
    intro x hx
    have hinterval : [[left, right]] = Set.Icc left right :=
      Set.uIcc_of_le hleft_right
    have hx_Icc : x ∈ Set.Icc left right :=
      hinterval ▸ hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le hleft hx_Icc.1
    exact
      Complex.norm_quadraticOscillationIntegrationCoefficientDerivative_eq_invSquare
        frequency x hfrequency hx_pos
  have hintegral_congr :
      (∫ x in left..right,
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x‖) =
        ∫ x in left..right,
          (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹ :=
    intervalIntegral.integral_congr hintegrands
  have hconstant_out :
      (∫ x in left..right,
          (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹) =
        (2 * ‖frequency‖)⁻¹ *
          ∫ x in left..right, (x ^ 2)⁻¹ :=
    intervalIntegral.integral_const_mul
      (2 * ‖frequency‖)⁻¹
      (fun x : ℝ => (x ^ 2)⁻¹)
  exact
    hintegral_congr.trans
      (hconstant_out.trans
        (congrArg
          (fun value : ℝ => (2 * ‖frequency‖)⁻¹ * value)
          (Real.intervalIntegral_square_inv
            left right hleft hleft_right)))

/-- Positive-half-line endpoint form of the reciprocal coefficient norm. -/
theorem Complex.norm_quadraticOscillationIntegrationCoefficient_eq_scaleInv_mul_xInv
    (frequency x : ℝ)
    (hx : 0 < x) :
    ‖Complex.quadraticOscillationIntegrationCoefficient frequency x‖ =
      (2 * ‖frequency‖)⁻¹ * x⁻¹ := by
  have hx_norm : ‖x‖ = x :=
    Real.norm_of_nonneg (le_of_lt hx)
  have hraw :
      ‖Complex.quadraticOscillationIntegrationCoefficient frequency x‖ =
        (2 * ‖frequency‖ * x)⁻¹ :=
    (Complex.norm_quadraticOscillationIntegrationCoefficient frequency x).trans
      (congrArg
        (fun coordinate : ℝ => (2 * ‖frequency‖ * coordinate)⁻¹)
        hx_norm)
  have hinverse_product :
      (2 * ‖frequency‖ * x)⁻¹ = x⁻¹ * (2 * ‖frequency‖)⁻¹ :=
    mul_inv_rev (2 * ‖frequency‖) x
  have hcommute :
      x⁻¹ * (2 * ‖frequency‖)⁻¹ =
        (2 * ‖frequency‖)⁻¹ * x⁻¹ :=
    mul_comm x⁻¹ (2 * ‖frequency‖)⁻¹
  exact hraw.trans (hinverse_product.trans hcommute)

/-- Fully explicit finite quadratic-tail estimate.  No limiting argument is
used: both endpoints and the exact inverse-square variation are retained. -/
theorem Complex.norm_intervalIntegral_quadraticOscillation_le_explicit_tail
    (frequency left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
        Complex.quadraticOscillation frequency x‖ ≤
      (2 * ‖frequency‖)⁻¹ * right⁻¹ +
        (2 * ‖frequency‖)⁻¹ * left⁻¹ +
        (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹) := by
  have hright : 0 < right :=
    lt_of_lt_of_le hleft hleft_right
  have hstructural :=
    Complex.norm_intervalIntegral_quadraticOscillation_le_boundary_add_remainder
      frequency left right hfrequency hleft hleft_right
  have hright_coefficient :
      ‖Complex.quadraticOscillationIntegrationCoefficient frequency right‖ =
        (2 * ‖frequency‖)⁻¹ * right⁻¹ :=
    Complex.norm_quadraticOscillationIntegrationCoefficient_eq_scaleInv_mul_xInv
      frequency right hright
  have hleft_coefficient :
      ‖Complex.quadraticOscillationIntegrationCoefficient frequency left‖ =
        (2 * ‖frequency‖)⁻¹ * left⁻¹ :=
    Complex.norm_quadraticOscillationIntegrationCoefficient_eq_scaleInv_mul_xInv
      frequency left hleft
  have hremainder :
      (∫ x in left..right,
          ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
              frequency x‖) =
        (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹) :=
    Complex.intervalIntegral_norm_quadraticOscillationIntegrationCoefficientDerivative
      frequency left right hfrequency hleft hleft_right
  have hright_side :
      ‖Complex.quadraticOscillationIntegrationCoefficient frequency right‖ +
          ‖Complex.quadraticOscillationIntegrationCoefficient frequency left‖ +
          ∫ x in left..right,
            ‖Complex.quadraticOscillationIntegrationCoefficientDerivative
                frequency x‖ =
        (2 * ‖frequency‖)⁻¹ * right⁻¹ +
          (2 * ‖frequency‖)⁻¹ * left⁻¹ +
          (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹) :=
    congrArg₂ (fun boundary remainder : ℝ => boundary + remainder)
      (congrArg₂ (fun u v : ℝ => u + v)
        hright_coefficient hleft_coefficient)
      hremainder
  exact le_trans hstructural (le_of_eq hright_side)

/-- The three terms in the explicit quadratic-tail budget collapse exactly:
the far-endpoint contribution cancels against the variation decrement. -/
theorem Real.quadraticTail_budget_eq_two_leftEndpoint
    (scaleInv leftInv rightInv : ℝ) :
    scaleInv * rightInv + scaleInv * leftInv +
        scaleInv * (leftInv - rightInv) =
      (scaleInv + scaleInv) * leftInv := by
  have hdistribute :
      scaleInv * (leftInv - rightInv) =
        scaleInv * leftInv - scaleInv * rightInv :=
    mul_sub scaleInv leftInv rightInv
  have hreorder :
      scaleInv * rightInv + scaleInv * leftInv +
          (scaleInv * leftInv - scaleInv * rightInv) =
        (scaleInv * leftInv + scaleInv * leftInv) +
          scaleInv * rightInv - scaleInv * rightInv := by
    calc
      scaleInv * rightInv + scaleInv * leftInv +
          (scaleInv * leftInv - scaleInv * rightInv) =
        (scaleInv * rightInv + scaleInv * leftInv +
          scaleInv * leftInv) - scaleInv * rightInv := by
            exact
              (add_sub_assoc
                (scaleInv * rightInv + scaleInv * leftInv)
                (scaleInv * leftInv)
                (scaleInv * rightInv)).symm
      _ = ((scaleInv * leftInv + scaleInv * leftInv) +
          scaleInv * rightInv) - scaleInv * rightInv := by
            exact congrArg
              (fun value : ℝ => value - scaleInv * rightInv)
              (calc
                scaleInv * rightInv + scaleInv * leftInv +
                    scaleInv * leftInv =
                  scaleInv * rightInv +
                    (scaleInv * leftInv + scaleInv * leftInv) :=
                  add_assoc
                    (scaleInv * rightInv)
                    (scaleInv * leftInv)
                    (scaleInv * leftInv)
                _ = (scaleInv * leftInv + scaleInv * leftInv) +
                    scaleInv * rightInv :=
                  add_comm
                    (scaleInv * rightInv)
                    (scaleInv * leftInv + scaleInv * leftInv))
  calc
    scaleInv * rightInv + scaleInv * leftInv +
        scaleInv * (leftInv - rightInv) =
      scaleInv * rightInv + scaleInv * leftInv +
        (scaleInv * leftInv - scaleInv * rightInv) := by
          exact congrArg
            (fun value : ℝ =>
              scaleInv * rightInv + scaleInv * leftInv + value)
            hdistribute
    _ = (scaleInv * leftInv + scaleInv * leftInv) +
        scaleInv * rightInv - scaleInv * rightInv :=
      hreorder
    _ = scaleInv * leftInv + scaleInv * leftInv :=
      add_sub_cancel_right
        (scaleInv * leftInv + scaleInv * leftInv)
        (scaleInv * rightInv)
    _ = (scaleInv + scaleInv) * leftInv :=
      (add_mul scaleInv scaleInv leftInv).symm

/-- Simplified positive quadratic-tail bound depending only on the near
endpoint.  This is the form used in Cauchy and improper-integral arguments. -/
theorem Complex.norm_intervalIntegral_quadraticOscillation_le_two_leftEndpoint
    (frequency left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
        Complex.quadraticOscillation frequency x‖ ≤
      ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹ := by
  have hraw :=
    Complex.norm_intervalIntegral_quadraticOscillation_le_explicit_tail
      frequency left right hfrequency hleft hleft_right
  have hcollapse :=
    Real.quadraticTail_budget_eq_two_leftEndpoint
      (2 * ‖frequency‖)⁻¹ left⁻¹ right⁻¹
  exact le_trans hraw (le_of_eq hcollapse)

/-- Pure quadratic oscillation is even. -/
theorem Complex.quadraticOscillation_neg
    (frequency x : ℝ) :
    Complex.quadraticOscillation frequency (-x) =
      Complex.quadraticOscillation frequency x := by
  have hcast_neg : (((-x : ℝ) : ℂ)) = -(x : ℂ) :=
    Complex.ofReal_neg x
  have hsquare : (((-x : ℝ) : ℂ)) ^ 2 = ((x : ℂ) ^ 2) := by
    calc
      (((-x : ℝ) : ℂ)) ^ 2 = (-(x : ℂ)) ^ 2 :=
        congrArg (fun value : ℂ => value ^ 2) hcast_neg
      _ = (x : ℂ) ^ 2 := neg_sq (x : ℂ)
  exact
    congrArg Complex.exp
      (congrArg
        (fun square : ℂ =>
          (Complex.I * (frequency : ℂ)) * square)
        hsquare)

/-- Reflection transports a negative quadratic tail to the corresponding
positive tail. -/
theorem Complex.intervalIntegral_quadraticOscillation_neg_reflection
    (frequency left right : ℝ) :
    (∫ x in -right..-left,
        Complex.quadraticOscillation frequency x) =
      ∫ x in left..right,
        Complex.quadraticOscillation frequency x := by
  have hreflection :
      (∫ x in left..right,
          Complex.quadraticOscillation frequency (-x)) =
        ∫ x in -right..-left,
          Complex.quadraticOscillation frequency x :=
    intervalIntegral.integral_comp_neg
      (fun x : ℝ => Complex.quadraticOscillation frequency x)
  have heven :
      (∫ x in left..right,
          Complex.quadraticOscillation frequency (-x)) =
        ∫ x in left..right,
          Complex.quadraticOscillation frequency x := by
    exact intervalIntegral.integral_congr
      (fun x _hx => Complex.quadraticOscillation_neg frequency x)
  exact hreflection.symm.trans heven

/-- The negative quadratic tail obeys the same explicit near-endpoint bound
as the reflected positive tail. -/
theorem Complex.norm_intervalIntegral_quadraticOscillation_negativeTail_le_two_nearEndpoint
    (frequency left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in -right..-left,
        Complex.quadraticOscillation frequency x‖ ≤
      ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹ := by
  have hpositive :=
    Complex.norm_intervalIntegral_quadraticOscillation_le_two_leftEndpoint
      frequency left right hfrequency hleft hleft_right
  have hreflection :=
    Complex.intervalIntegral_quadraticOscillation_neg_reflection
      frequency left right
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹)
      hreflection.symm
      hpositive

/-- Explicit two-sided annular tail estimate for symmetric quadratic
truncations. -/
theorem Complex.norm_quadraticOscillation_symmetricAnnulus_le
    (frequency inner outer : ℝ)
    (hfrequency : frequency ≠ 0)
    (hinner : 0 < inner)
    (hinner_outer : inner ≤ outer) :
    ‖(∫ x in -outer..-inner,
          Complex.quadraticOscillation frequency x) +
        (∫ x in inner..outer,
          Complex.quadraticOscillation frequency x)‖ ≤
      (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * inner⁻¹) +
        (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * inner⁻¹) := by
  have hnegative :=
    Complex.norm_intervalIntegral_quadraticOscillation_negativeTail_le_two_nearEndpoint
      frequency inner outer hfrequency hinner hinner_outer
  have hpositive :=
    Complex.norm_intervalIntegral_quadraticOscillation_le_two_leftEndpoint
      frequency inner outer hfrequency hinner hinner_outer
  have htriangle :
      ‖(∫ x in -outer..-inner,
          Complex.quadraticOscillation frequency x) +
        (∫ x in inner..outer,
          Complex.quadraticOscillation frequency x)‖ ≤
        ‖∫ x in -outer..-inner,
          Complex.quadraticOscillation frequency x‖ +
        ‖∫ x in inner..outer,
          Complex.quadraticOscillation frequency x‖ :=
    norm_add_le
      (∫ x in -outer..-inner,
        Complex.quadraticOscillation frequency x)
      (∫ x in inner..outer,
        Complex.quadraticOscillation frequency x)
  exact le_trans htriangle (add_le_add hnegative hpositive)

/-- Additive algebra for removing a middle interval from a three-piece
decomposition. -/
theorem Complex.threePiece_sub_middle
    (whole left middle right : ℂ)
    (hwhole : whole = (left + middle) + right) :
    whole - middle = left + right := by
  have hreorder :
      (left + middle) + right = (left + right) + middle := by
    calc
      (left + middle) + right = left + (middle + right) :=
        add_assoc left middle right
      _ = left + (right + middle) :=
        congrArg (fun value : ℂ => left + value)
          (add_comm middle right)
      _ = (left + right) + middle :=
        (add_assoc left right middle).symm
  calc
    whole - middle = ((left + middle) + right) - middle :=
      congrArg (fun value : ℂ => value - middle) hwhole
    _ = ((left + right) + middle) - middle :=
      congrArg (fun value : ℂ => value - middle) hreorder
    _ = left + right := add_sub_cancel_right (left + right) middle

/-- Exact difference of two symmetric quadratic truncations: only the two
outer annular tails remain. -/
theorem Complex.intervalIntegral_quadraticOscillation_symmetricTruncation_sub
    (frequency inner outer : ℝ)
    (_hinner_outer : inner ≤ outer) :
    (∫ x in -outer..outer,
        Complex.quadraticOscillation frequency x) -
      (∫ x in -inner..inner,
        Complex.quadraticOscillation frequency x) =
      (∫ x in -outer..-inner,
          Complex.quadraticOscillation frequency x) +
        (∫ x in inner..outer,
          Complex.quadraticOscillation frequency x) := by
  let f : ℝ → ℂ := Complex.quadraticOscillation frequency
  have hf : Continuous f :=
    Complex.continuous_quadraticOscillation frequency
  have hleft : IntervalIntegrable f MeasureTheory.volume (-outer) (-inner) :=
    hf.intervalIntegrable (-outer) (-inner)
  have hmiddle : IntervalIntegrable f MeasureTheory.volume (-inner) inner :=
    hf.intervalIntegrable (-inner) inner
  have hright : IntervalIntegrable f MeasureTheory.volume inner outer :=
    hf.intervalIntegrable inner outer
  have hleft_middle :
      (∫ x in -outer..-inner, f x) +
          (∫ x in -inner..inner, f x) =
        ∫ x in -outer..inner, f x :=
    intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  have hwhole_raw :
      (∫ x in -outer..inner, f x) +
          (∫ x in inner..outer, f x) =
        ∫ x in -outer..outer, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hleft.trans hmiddle) hright
  have hwhole :
      (∫ x in -outer..outer, f x) =
        ((∫ x in -outer..-inner, f x) +
          (∫ x in -inner..inner, f x)) +
            (∫ x in inner..outer, f x) := by
    exact hwhole_raw.symm.trans
      (congrArg
        (fun value : ℂ => value + ∫ x in inner..outer, f x)
        hleft_middle.symm)
  exact
    Complex.threePiece_sub_middle
      (∫ x in -outer..outer, f x)
      (∫ x in -outer..-inner, f x)
      (∫ x in -inner..inner, f x)
      (∫ x in inner..outer, f x)
      hwhole

/-- Quantitative Cauchy estimate for symmetric quadratic truncations. -/
theorem Complex.norm_intervalIntegral_quadraticOscillation_symmetricTruncation_sub_le
    (frequency inner outer : ℝ)
    (hfrequency : frequency ≠ 0)
    (hinner : 0 < inner)
    (hinner_outer : inner ≤ outer) :
    ‖(∫ x in -outer..outer,
          Complex.quadraticOscillation frequency x) -
        (∫ x in -inner..inner,
          Complex.quadraticOscillation frequency x)‖ ≤
      (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * inner⁻¹) +
        (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * inner⁻¹) := by
  have hdecomposition :=
    Complex.intervalIntegral_quadraticOscillation_symmetricTruncation_sub
      frequency inner outer hinner_outer
  have htail :=
    Complex.norm_quadraticOscillation_symmetricAnnulus_le
      frequency inner outer hfrequency hinner hinner_outer
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * inner⁻¹) +
            (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * inner⁻¹))
      hdecomposition.symm
      htail

/-- Symmetric integer-radius truncation of the quadratic oscillatory
integral.  The successor radius keeps every truncation away from zero. -/
def Complex.quadraticOscillationSymmetricTruncation
    (frequency : ℝ)
    (n : ℕ) : ℂ :=
  ∫ x in -(((n + 1 : ℕ) : ℝ))..(((n + 1 : ℕ) : ℝ)),
    Complex.quadraticOscillation frequency x

/-- Explicit Cauchy budget for the symmetric integer-radius truncations. -/
def Complex.quadraticOscillationSymmetricTailBudget
    (frequency : ℝ)
    (n : ℕ) : ℝ :=
  (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) *
      (((n + 1 : ℕ) : ℝ))⁻¹) +
    (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) *
      (((n + 1 : ℕ) : ℝ))⁻¹)

/-- The explicit symmetric-tail budget tends to zero. -/
theorem Complex.tendsto_quadraticOscillationSymmetricTailBudget_zero
    (frequency : ℝ) :
    Filter.Tendsto
      (Complex.quadraticOscillationSymmetricTailBudget frequency)
      Filter.atTop
      (𝓝 0) := by
  let coefficient : ℝ :=
    (2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹
  have hinverse :
      Filter.Tendsto
        (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹)
        Filter.atTop
        (𝓝 0) :=
    tendsto_inverse_atTop_nhds_zero_nat.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hterm_raw :
      Filter.Tendsto
        (fun n : ℕ => coefficient * (((n + 1 : ℕ) : ℝ))⁻¹)
        Filter.atTop
        (𝓝 (coefficient * 0)) :=
    tendsto_const_nhds.mul hinverse
  have hterm :
      Filter.Tendsto
        (fun n : ℕ => coefficient * (((n + 1 : ℕ) : ℝ))⁻¹)
        Filter.atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Filter.Tendsto
          (fun n : ℕ => coefficient * (((n + 1 : ℕ) : ℝ))⁻¹)
          Filter.atTop
          (𝓝 value))
      (mul_zero coefficient)
      hterm_raw
  have hsum_raw :
      Filter.Tendsto
        (fun n : ℕ =>
          coefficient * (((n + 1 : ℕ) : ℝ))⁻¹ +
            coefficient * (((n + 1 : ℕ) : ℝ))⁻¹)
        Filter.atTop
        (𝓝 (0 + 0)) :=
    hterm.add hterm
  have hsum :
      Filter.Tendsto
        (fun n : ℕ =>
          coefficient * (((n + 1 : ℕ) : ℝ))⁻¹ +
            coefficient * (((n + 1 : ℕ) : ℝ))⁻¹)
        Filter.atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Filter.Tendsto
          (fun n : ℕ =>
            coefficient * (((n + 1 : ℕ) : ℝ))⁻¹ +
              coefficient * (((n + 1 : ℕ) : ℝ))⁻¹)
          Filter.atTop
          (𝓝 value))
      (zero_add 0)
      hsum_raw
  exact hsum

/-- Quantitative comparison of two integer-radius symmetric truncations. -/
theorem Complex.norm_quadraticOscillationSymmetricTruncation_sub_le_budget
    (frequency : ℝ)
    (hfrequency : frequency ≠ 0)
    {inner outer : ℕ}
    (hinner_outer : inner ≤ outer) :
    ‖Complex.quadraticOscillationSymmetricTruncation frequency outer -
        Complex.quadraticOscillationSymmetricTruncation frequency inner‖ ≤
      Complex.quadraticOscillationSymmetricTailBudget frequency inner := by
  have hinner_pos : 0 < (((inner + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ inner)
  have hradius_order :
      (((inner + 1 : ℕ) : ℝ)) ≤ (((outer + 1 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.add_le_add_right hinner_outer 1)
  exact
    Complex.norm_intervalIntegral_quadraticOscillation_symmetricTruncation_sub_le
      frequency
      (((inner + 1 : ℕ) : ℝ))
      (((outer + 1 : ℕ) : ℝ))
      hfrequency hinner_pos hradius_order

/-- Symmetric quadratic truncations form a Cauchy sequence. -/
theorem Complex.cauchySeq_quadraticOscillationSymmetricTruncation
    (frequency : ℝ)
    (hfrequency : frequency ≠ 0) :
    CauchySeq
      (Complex.quadraticOscillationSymmetricTruncation frequency) := by
  exact Metric.cauchySeq_iff'.mpr
    (fun epsilon hepsilon => by
      have heventually :
          ∀ᶠ n : ℕ in Filter.atTop,
            Complex.quadraticOscillationSymmetricTailBudget frequency n <
              epsilon :=
        (Complex.tendsto_quadraticOscillationSymmetricTailBudget_zero frequency).eventually
          (Iio_mem_nhds hepsilon)
      match Filter.eventually_atTop.1 heventually with
      | ⟨N, hN⟩ =>
          exact
            ⟨N, fun n hn => by
              have hnorm :=
                Complex.norm_quadraticOscillationSymmetricTruncation_sub_le_budget
                  frequency hfrequency hn
              have hbudget :
                  Complex.quadraticOscillationSymmetricTailBudget frequency N <
                    epsilon :=
                hN N le_rfl
              have hnorm_lt :
                  ‖Complex.quadraticOscillationSymmetricTruncation frequency n -
                      Complex.quadraticOscillationSymmetricTruncation frequency N‖ <
                    epsilon :=
                lt_of_le_of_lt hnorm hbudget
              exact
                Eq.subst
                  (motive := fun value : ℝ => value < epsilon)
                  (dist_eq_norm
                    (Complex.quadraticOscillationSymmetricTruncation frequency n)
                    (Complex.quadraticOscillationSymmetricTruncation frequency N)).symm
                  hnorm_lt⟩)

/-- The genuine improper quadratic oscillatory integral, defined as the limit
of symmetric integer-radius truncations. -/
def Complex.quadraticOscillatoryImproperIntegral
    (frequency : ℝ) : ℂ :=
  limUnder Filter.atTop
    (Complex.quadraticOscillationSymmetricTruncation frequency)

/-- The symmetric truncations converge to the improper quadratic oscillatory
integral. -/
theorem Complex.tendsto_quadraticOscillationSymmetricTruncation_improperIntegral
    (frequency : ℝ)
    (hfrequency : frequency ≠ 0) :
    Filter.Tendsto
      (Complex.quadraticOscillationSymmetricTruncation frequency)
      Filter.atTop
      (𝓝 (Complex.quadraticOscillatoryImproperIntegral frequency)) := by
  have hconverges :
      ∃ value : ℂ,
        Filter.Tendsto
          (Complex.quadraticOscillationSymmetricTruncation frequency)
          Filter.atTop
          (𝓝 value) :=
    cauchySeq_tendsto_of_complete
      (Complex.cauchySeq_quadraticOscillationSymmetricTruncation
        frequency hfrequency)
  exact tendsto_nhds_limUnder hconverges

/-- Quadratic oscillation written around an arbitrary stationary centre. -/
def Complex.centeredQuadraticOscillation
    (frequency center x : ℝ) : ℂ :=
  Complex.quadraticOscillation frequency (x - center)

/-- Translation transports a centred quadratic oscillation to the pure
quadratic oscillation. -/
theorem Complex.intervalIntegral_centeredQuadraticOscillation_eq_translated
    (frequency center left right : ℝ) :
    (∫ x in left..right,
        Complex.centeredQuadraticOscillation frequency center x) =
      ∫ x in left - center..right - center,
        Complex.quadraticOscillation frequency x := by
  exact
    intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => Complex.quadraticOscillation frequency x)
      center

/-- A centred quadratic tail inherits the explicit positive-side estimate once
the translated interval lies to the right of its stationary centre. -/
theorem Complex.norm_intervalIntegral_centeredQuadraticOscillation_le_explicit_tail
    (frequency center left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hcenter_left : center < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
        Complex.centeredQuadraticOscillation frequency center x‖ ≤
      (2 * ‖frequency‖)⁻¹ * (left - center)⁻¹ +
        (2 * ‖frequency‖)⁻¹ * (right - center)⁻¹ +
        (2 * ‖frequency‖)⁻¹ *
          ((left - center)⁻¹ - (right - center)⁻¹) := by
  have htranslated_left : 0 < left - center :=
    sub_pos.mpr hcenter_left
  have htranslated_order : left - center ≤ right - center :=
    sub_le_sub_right hleft_right center
  have htranslated :=
    Complex.norm_intervalIntegral_quadraticOscillation_le_explicit_tail
      frequency (left - center) (right - center)
      hfrequency htranslated_left htranslated_order
  have htransport :=
    Complex.intervalIntegral_centeredQuadraticOscillation_eq_translated
      frequency center left right
  have hbound_reorder :
      (2 * ‖frequency‖)⁻¹ * (right - center)⁻¹ +
          (2 * ‖frequency‖)⁻¹ * (left - center)⁻¹ +
          (2 * ‖frequency‖)⁻¹ *
            ((left - center)⁻¹ - (right - center)⁻¹) =
        (2 * ‖frequency‖)⁻¹ * (left - center)⁻¹ +
          (2 * ‖frequency‖)⁻¹ * (right - center)⁻¹ +
          (2 * ‖frequency‖)⁻¹ *
            ((left - center)⁻¹ - (right - center)⁻¹) :=
    congrArg
      (fun value : ℝ =>
        value +
          (2 * ‖frequency‖)⁻¹ *
            ((left - center)⁻¹ - (right - center)⁻¹))
      (add_comm
        ((2 * ‖frequency‖)⁻¹ * (right - center)⁻¹)
        ((2 * ‖frequency‖)⁻¹ * (left - center)⁻¹))
  have htranslated_ordered :
      ‖∫ x in left - center..right - center,
          Complex.quadraticOscillation frequency x‖ ≤
        (2 * ‖frequency‖)⁻¹ * (left - center)⁻¹ +
          (2 * ‖frequency‖)⁻¹ * (right - center)⁻¹ +
          (2 * ‖frequency‖)⁻¹ *
            ((left - center)⁻¹ - (right - center)⁻¹) :=
    le_trans htranslated (le_of_eq hbound_reorder)
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          (2 * ‖frequency‖)⁻¹ * (left - center)⁻¹ +
            (2 * ‖frequency‖)⁻¹ * (right - center)⁻¹ +
            (2 * ‖frequency‖)⁻¹ *
              ((left - center)⁻¹ - (right - center)⁻¹))
      htransport.symm
      htranslated_ordered

/-- Simplified centered quadratic tail bound, expressed only through the
distance from the stationary center to the near endpoint. -/
theorem Complex.norm_intervalIntegral_centeredQuadraticOscillation_le_two_nearEndpoint
    (frequency center left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hcenter_left : center < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
        Complex.centeredQuadraticOscillation frequency center x‖ ≤
      ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) *
        (left - center)⁻¹ := by
  have htranslated_left : 0 < left - center :=
    sub_pos.mpr hcenter_left
  have htranslated_order : left - center ≤ right - center :=
    sub_le_sub_right hleft_right center
  have htail :=
    Complex.norm_intervalIntegral_quadraticOscillation_le_two_leftEndpoint
      frequency (left - center) (right - center)
      hfrequency htranslated_left htranslated_order
  have htransport :=
    Complex.intervalIntegral_centeredQuadraticOscillation_eq_translated
      frequency center left right
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) *
            (left - center)⁻¹)
      htransport.symm
      htail

end

end LFunctions
end Boundary
