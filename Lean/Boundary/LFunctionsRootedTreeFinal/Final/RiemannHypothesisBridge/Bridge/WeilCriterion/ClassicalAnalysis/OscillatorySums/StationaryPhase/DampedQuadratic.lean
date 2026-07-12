import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.IntegrationByParts
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.StationaryPhase.QuadraticTail

/-!
# Damped quadratic oscillatory integrals

This file owns the Gaussian regularization used in the finite stationary-phase
argument.  A positive real damping parameter moves the quadratic coefficient
into the open left half-plane, where the complex Gaussian integral is
absolutely integrable and has an exact closed form.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval Topology

/-- Complex quadratic coefficient with Gaussian damping `epsilon` and real
oscillatory frequency `frequency`. -/
def Complex.dampedQuadraticCoefficient
    (epsilon frequency : ℝ) : ℂ :=
  -(epsilon : ℂ) + Complex.I * (frequency : ℂ)

/-- Gaussian-damped quadratic oscillator. -/
def Complex.dampedQuadraticOscillator
    (epsilon frequency x : ℝ) : ℂ :=
  Complex.exp
    (Complex.dampedQuadraticCoefficient epsilon frequency * (x : ℂ) ^ 2)

/-- Derivative denominator of the damped quadratic oscillator. -/
def Complex.dampedQuadraticDerivativeDenominator
    (epsilon frequency x : ℝ) : ℂ :=
  2 * Complex.dampedQuadraticCoefficient epsilon frequency * (x : ℂ)

/-- Reciprocal coefficient used for uniform damped-tail integration by parts. -/
def Complex.dampedQuadraticIntegrationCoefficient
    (epsilon frequency x : ℝ) : ℂ :=
  (Complex.dampedQuadraticDerivativeDenominator epsilon frequency x)⁻¹

/-- Named derivative of the damped quadratic oscillator. -/
def Complex.dampedQuadraticOscillatorDerivative
    (epsilon frequency x : ℝ) : ℂ :=
  Complex.dampedQuadraticOscillator epsilon frequency x *
    Complex.dampedQuadraticDerivativeDenominator epsilon frequency x

/-- Named derivative of the reciprocal damped quadratic coefficient. -/
def Complex.dampedQuadraticIntegrationCoefficientDerivative
    (epsilon frequency x : ℝ) : ℂ :=
  -(2 * Complex.dampedQuadraticCoefficient epsilon frequency) /
    (Complex.dampedQuadraticDerivativeDenominator epsilon frequency x) ^ 2

/-- Real part of the damped quadratic coefficient. -/
theorem Complex.dampedQuadraticCoefficient_re
    (epsilon frequency : ℝ) :
    ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ))).re = -epsilon := by
  have hneg : (-(epsilon : ℂ)).re = -epsilon :=
    (Complex.neg_re (epsilon : ℂ)).trans
      (congrArg Neg.neg (Complex.ofReal_re epsilon))
  have hproduct : (Complex.I * (frequency : ℂ)).re = 0 := by
    calc
      (Complex.I * (frequency : ℂ)).re =
          Complex.I.re * (frequency : ℂ).re -
            Complex.I.im * (frequency : ℂ).im :=
        Complex.mul_re Complex.I (frequency : ℂ)
      _ = 0 * frequency - 1 * 0 :=
        congrArg₂ Sub.sub
          (congrArg₂ HMul.hMul Complex.I_re
            (Complex.ofReal_re frequency))
          (congrArg₂ HMul.hMul Complex.I_im
            (Complex.ofReal_im frequency))
      _ = 0 * frequency - 0 :=
        congrArg (fun value : ℝ => 0 * frequency - value)
          (one_mul (0 : ℝ))
      _ = 0 * frequency := sub_zero (0 * frequency)
      _ = 0 := zero_mul frequency
  calc
    ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ))).re =
        (-(epsilon : ℂ)).re +
          (Complex.I * (frequency : ℂ)).re :=
      Complex.add_re (-(epsilon : ℂ)) (Complex.I * (frequency : ℂ))
    _ = -epsilon + 0 := congrArg₂ HAdd.hAdd hneg hproduct
    _ = -epsilon := add_zero (-epsilon)

/-- Imaginary part of the damped quadratic coefficient. -/
theorem Complex.dampedQuadraticCoefficient_im
    (epsilon frequency : ℝ) :
    (Complex.dampedQuadraticCoefficient epsilon frequency).im = frequency := by
  have hcoefficient :
      Complex.dampedQuadraticCoefficient epsilon frequency =
        -(epsilon : ℂ) + (frequency : ℂ) * Complex.I := by
    exact congrArg
      (fun value : ℂ => -(epsilon : ℂ) + value)
      (mul_comm Complex.I (frequency : ℂ))
  have hneg_im : (-(epsilon : ℂ)).im = 0 := by
    exact
      (Complex.neg_im (epsilon : ℂ)).trans
        ((congrArg Neg.neg (Complex.ofReal_im epsilon)).trans (neg_zero))
  have hfrequency_I_im :
      ((frequency : ℂ) * Complex.I).im = frequency := by
    have hmul := Complex.mul_im (frequency : ℂ) Complex.I
    exact
      hmul.trans
        (calc
          (frequency : ℂ).re * Complex.I.im +
              (frequency : ℂ).im * Complex.I.re =
            frequency * Complex.I.im +
              (frequency : ℂ).im * Complex.I.re := by
                exact congrArg
                  (fun value : ℝ =>
                    value * Complex.I.im +
                      (frequency : ℂ).im * Complex.I.re)
                  (Complex.ofReal_re frequency)
          _ = frequency * 1 + (frequency : ℂ).im * Complex.I.re := by
                exact congrArg
                  (fun value : ℝ =>
                    frequency * value +
                      (frequency : ℂ).im * Complex.I.re)
                  Complex.I_im
          _ = frequency * 1 + 0 * Complex.I.re := by
                exact congrArg
                  (fun value : ℝ =>
                    frequency * 1 + value * Complex.I.re)
                  (Complex.ofReal_im frequency)
          _ = frequency * 1 + 0 * 0 := by
                exact congrArg
                  (fun value : ℝ => frequency * 1 + 0 * value)
                  Complex.I_re
          _ = frequency := by
                exact
                  (congrArg₂ HAdd.hAdd
                    (mul_one frequency)
                    (zero_mul 0)).trans
                    (add_zero frequency))
  calc
    (Complex.dampedQuadraticCoefficient epsilon frequency).im =
        (-(epsilon : ℂ) + (frequency : ℂ) * Complex.I).im :=
      congrArg Complex.im hcoefficient
    _ = (-(epsilon : ℂ)).im +
        ((frequency : ℂ) * Complex.I).im :=
      Complex.add_im (-(epsilon : ℂ)) ((frequency : ℂ) * Complex.I)
    _ = 0 + frequency :=
      congrArg₂ HAdd.hAdd hneg_im hfrequency_I_im
    _ = frequency := zero_add frequency

/-- The oscillatory frequency uniformly controls the norm of the damped
quadratic coefficient, independently of the damping parameter. -/
theorem Complex.norm_frequency_le_norm_dampedQuadraticCoefficient
    (epsilon frequency : ℝ) :
    ‖frequency‖ ≤
      ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ := by
  have him_le :
      |(Complex.dampedQuadraticCoefficient epsilon frequency).im| ≤
        Complex.abs
          (Complex.dampedQuadraticCoefficient epsilon frequency) :=
    Complex.abs_im_le_abs
      (Complex.dampedQuadraticCoefficient epsilon frequency)
  have him :
      |(Complex.dampedQuadraticCoefficient epsilon frequency).im| =
        |frequency| :=
    congrArg abs
      (Complex.dampedQuadraticCoefficient_im epsilon frequency)
  have hfrequency : ‖frequency‖ = |frequency| :=
    Real.norm_eq_abs frequency
  have hcoefficient :
      ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ =
        Complex.abs
          (Complex.dampedQuadraticCoefficient epsilon frequency) :=
    Complex.norm_eq_abs
      (Complex.dampedQuadraticCoefficient epsilon frequency)
  calc
    ‖frequency‖ = |frequency| := hfrequency
    _ = |(Complex.dampedQuadraticCoefficient epsilon frequency).im| :=
      him.symm
    _ ≤ Complex.abs
        (Complex.dampedQuadraticCoefficient epsilon frequency) := him_le
    _ = ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ :=
      hcoefficient.symm

/-- Nonzero real frequency makes every damped quadratic coefficient nonzero,
including at zero damping. -/
theorem Complex.dampedQuadraticCoefficient_ne_zero_of_frequency_ne_zero
    (epsilon frequency : ℝ)
    (hfrequency : frequency ≠ 0) :
    Complex.dampedQuadraticCoefficient epsilon frequency ≠ 0 := by
  intro hzero
  have hnorm_zero :
      ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ = 0 :=
    (congrArg norm hzero).trans (norm_zero : ‖(0 : ℂ)‖ = 0)
  have hfrequency_norm_le_zero : ‖frequency‖ ≤ 0 :=
    Eq.subst
      (motive := fun value : ℝ => ‖frequency‖ ≤ value)
      hnorm_zero
      (Complex.norm_frequency_le_norm_dampedQuadraticCoefficient
        epsilon frequency)
  have hfrequency_norm_zero : ‖frequency‖ = 0 :=
    le_antisymm hfrequency_norm_le_zero (norm_nonneg frequency)
  exact hfrequency (norm_eq_zero.mp hfrequency_norm_zero)

/-- The damped quadratic derivative denominator is nonzero away from the
stationary point whenever the real frequency is nonzero. -/
theorem Complex.dampedQuadraticDerivativeDenominator_ne_zero
    (epsilon frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : x ≠ 0) :
    Complex.dampedQuadraticDerivativeDenominator epsilon frequency x ≠ 0 := by
  have htwo : (2 : ℂ) ≠ 0 :=
    OfNat.ofNat_ne_zero 2
  have hcoefficient :
      Complex.dampedQuadraticCoefficient epsilon frequency ≠ 0 :=
    Complex.dampedQuadraticCoefficient_ne_zero_of_frequency_ne_zero
      epsilon frequency hfrequency
  have hx_cast : (x : ℂ) ≠ 0 := by
    intro hx_zero
    have hre : ((x : ℂ)).re = (0 : ℂ).re :=
      congrArg Complex.re hx_zero
    have hx_zero_real : x = 0 :=
      Eq.trans (Complex.ofReal_re x) hre
    exact hx hx_zero_real
  exact mul_ne_zero (mul_ne_zero htwo hcoefficient) hx_cast

/-- Reciprocal cancellation for the damped quadratic integration
coefficient. -/
theorem Complex.dampedQuadraticIntegrationCoefficient_mul_denominator
    (epsilon frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : x ≠ 0) :
    Complex.dampedQuadraticIntegrationCoefficient epsilon frequency x *
        Complex.dampedQuadraticDerivativeDenominator epsilon frequency x =
      1 := by
  exact inv_mul_cancel₀
    (Complex.dampedQuadraticDerivativeDenominator_ne_zero
      epsilon frequency x hfrequency hx)

/-- Exact derivative of the Gaussian-damped quadratic oscillator. -/
theorem Complex.hasDerivAt_dampedQuadraticOscillator
    (epsilon frequency x : ℝ) :
    HasDerivAt
      (Complex.dampedQuadraticOscillator epsilon frequency)
      (Complex.dampedQuadraticOscillator epsilon frequency x *
        Complex.dampedQuadraticDerivativeDenominator epsilon frequency x)
      x := by
  have hsquare :
      HasDerivAt
        (fun y : ℝ => (y : ℂ) ^ 2)
        (2 * (x : ℂ))
        x := by
    have hraw := (hasDerivAt_pow 2 (x : ℂ)).comp_ofReal
    have hindex : (2 - 1 : ℕ) = 1 := rfl
    have hpower : (x : ℂ) ^ (2 - 1) = (x : ℂ) :=
      (congrArg (fun n : ℕ => (x : ℂ) ^ n) hindex).trans
        (pow_one (x : ℂ))
    have hderivative :
        (2 : ℂ) * (x : ℂ) ^ (2 - 1) = 2 * (x : ℂ) :=
      congrArg (fun value : ℂ => (2 : ℂ) * value) hpower
    exact
      Eq.subst
        (motive := fun derivative : ℂ =>
          HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) derivative x)
        hderivative
        hraw
  have hexponent :
      HasDerivAt
        (fun y : ℝ =>
          Complex.dampedQuadraticCoefficient epsilon frequency *
            (y : ℂ) ^ 2)
        (Complex.dampedQuadraticCoefficient epsilon frequency *
          (2 * (x : ℂ)))
        x :=
    hsquare.const_mul
      (Complex.dampedQuadraticCoefficient epsilon frequency)
  have hraw := hexponent.cexp
  have hdenominator :
      Complex.dampedQuadraticCoefficient epsilon frequency *
          (2 * (x : ℂ)) =
        Complex.dampedQuadraticDerivativeDenominator epsilon frequency x := by
    calc
      Complex.dampedQuadraticCoefficient epsilon frequency *
          (2 * (x : ℂ)) =
        (Complex.dampedQuadraticCoefficient epsilon frequency * 2) *
          (x : ℂ) :=
        (mul_assoc
          (Complex.dampedQuadraticCoefficient epsilon frequency)
          2 (x : ℂ)).symm
      _ = (2 * Complex.dampedQuadraticCoefficient epsilon frequency) *
          (x : ℂ) :=
        congrArg
          (fun value : ℂ => value * (x : ℂ))
          (mul_comm
            (Complex.dampedQuadraticCoefficient epsilon frequency) 2)
      _ = Complex.dampedQuadraticDerivativeDenominator
          epsilon frequency x := rfl
  exact
    Eq.subst
      (motive := fun derivative : ℂ =>
        HasDerivAt
          (Complex.dampedQuadraticOscillator epsilon frequency)
          (Complex.dampedQuadraticOscillator epsilon frequency x * derivative)
          x)
      hdenominator
      hraw

/-- Exact derivative of the damped reciprocal integration coefficient. -/
theorem Complex.hasDerivAt_dampedQuadraticIntegrationCoefficient
    (epsilon frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : x ≠ 0) :
    HasDerivAt
      (Complex.dampedQuadraticIntegrationCoefficient epsilon frequency)
      (-(2 * Complex.dampedQuadraticCoefficient epsilon frequency) /
        (Complex.dampedQuadraticDerivativeDenominator
          epsilon frequency x) ^ 2)
      x := by
  let constant : ℂ :=
    2 * Complex.dampedQuadraticCoefficient epsilon frequency
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
      (Complex.dampedQuadraticDerivativeDenominator_ne_zero
        epsilon frequency x hfrequency hx)
  exact hcomplexInverse.comp_ofReal

/-- Pointwise cancellation of the reciprocal coefficient against the damped
oscillator derivative. -/
theorem Complex.dampedQuadraticIntegrationCoefficient_mul_deriv
    (epsilon frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : x ≠ 0) :
    Complex.dampedQuadraticIntegrationCoefficient epsilon frequency x *
        (Complex.dampedQuadraticOscillator epsilon frequency x *
          Complex.dampedQuadraticDerivativeDenominator epsilon frequency x) =
      Complex.dampedQuadraticOscillator epsilon frequency x := by
  let coefficient : ℂ :=
    Complex.dampedQuadraticIntegrationCoefficient epsilon frequency x
  let oscillator : ℂ :=
    Complex.dampedQuadraticOscillator epsilon frequency x
  let denominator : ℂ :=
    Complex.dampedQuadraticDerivativeDenominator epsilon frequency x
  have hcancellation : coefficient * denominator = 1 :=
    Complex.dampedQuadraticIntegrationCoefficient_mul_denominator
      epsilon frequency x hfrequency hx
  calc
    coefficient * (oscillator * denominator) =
        (coefficient * oscillator) * denominator :=
      (mul_assoc coefficient oscillator denominator).symm
    _ = (oscillator * coefficient) * denominator :=
      congrArg
        (fun value : ℂ => value * denominator)
        (mul_comm coefficient oscillator)
    _ = oscillator * (coefficient * denominator) :=
      mul_assoc oscillator coefficient denominator
    _ = oscillator * 1 :=
      congrArg (fun value : ℂ => oscillator * value) hcancellation
    _ = oscillator := mul_one oscillator

/-- The named damped oscillator derivative is the exact derivative. -/
theorem Complex.hasDerivAt_dampedQuadraticOscillator_named
    (epsilon frequency x : ℝ) :
    HasDerivAt
      (Complex.dampedQuadraticOscillator epsilon frequency)
      (Complex.dampedQuadraticOscillatorDerivative epsilon frequency x)
      x :=
  Complex.hasDerivAt_dampedQuadraticOscillator epsilon frequency x

/-- The named reciprocal-coefficient derivative is exact away from the
stationary point. -/
theorem Complex.hasDerivAt_dampedQuadraticIntegrationCoefficient_named
    (epsilon frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : x ≠ 0) :
    HasDerivAt
      (Complex.dampedQuadraticIntegrationCoefficient epsilon frequency)
      (Complex.dampedQuadraticIntegrationCoefficientDerivative
        epsilon frequency x)
      x :=
  Complex.hasDerivAt_dampedQuadraticIntegrationCoefficient
    epsilon frequency x hfrequency hx

/-- The damped quadratic derivative denominator varies continuously. -/
theorem Complex.continuous_dampedQuadraticDerivativeDenominator
    (epsilon frequency : ℝ) :
    Continuous
      (Complex.dampedQuadraticDerivativeDenominator epsilon frequency) := by
  have hconstant :
      Continuous
        (fun _ : ℝ =>
          2 * Complex.dampedQuadraticCoefficient epsilon frequency) :=
    continuous_const
  exact hconstant.mul Complex.continuous_ofReal

/-- The damped quadratic oscillator varies continuously. -/
theorem Complex.continuous_dampedQuadraticOscillator
    (epsilon frequency : ℝ) :
    Continuous
      (Complex.dampedQuadraticOscillator epsilon frequency) := by
  exact
    continuous_iff_continuousAt.mpr
      (fun x =>
        (Complex.hasDerivAt_dampedQuadraticOscillator_named
          epsilon frequency x).continuousAt)

/-- The named damped oscillator derivative varies continuously. -/
theorem Complex.continuous_dampedQuadraticOscillatorDerivative
    (epsilon frequency : ℝ) :
    Continuous
      (Complex.dampedQuadraticOscillatorDerivative epsilon frequency) := by
  exact
    (Complex.continuous_dampedQuadraticOscillator epsilon frequency).mul
      (Complex.continuous_dampedQuadraticDerivativeDenominator
        epsilon frequency)

/-- The reciprocal damped coefficient is continuous on sets avoiding the
stationary point. -/
theorem Complex.continuousOn_dampedQuadraticIntegrationCoefficient
    (epsilon frequency : ℝ)
    (hfrequency : frequency ≠ 0)
    (set : Set ℝ)
    (hset : ∀ x ∈ set, x ≠ 0) :
    ContinuousOn
      (Complex.dampedQuadraticIntegrationCoefficient epsilon frequency)
      set := by
  have hdenominator :
      ContinuousOn
        (Complex.dampedQuadraticDerivativeDenominator epsilon frequency)
        set :=
    (Complex.continuous_dampedQuadraticDerivativeDenominator
      epsilon frequency).continuousOn
  exact
    hdenominator.inv₀
      (fun x hx =>
        Complex.dampedQuadraticDerivativeDenominator_ne_zero
          epsilon frequency x hfrequency (hset x hx))

/-- The reciprocal-coefficient derivative is continuous on sets avoiding the
stationary point. -/
theorem Complex.continuousOn_dampedQuadraticIntegrationCoefficientDerivative
    (epsilon frequency : ℝ)
    (hfrequency : frequency ≠ 0)
    (set : Set ℝ)
    (hset : ∀ x ∈ set, x ≠ 0) :
    ContinuousOn
      (Complex.dampedQuadraticIntegrationCoefficientDerivative
        epsilon frequency)
      set := by
  have hnumerator :
      ContinuousOn
        (fun _ : ℝ =>
          -(2 * Complex.dampedQuadraticCoefficient epsilon frequency))
        set :=
    continuousOn_const
  have hdenominator :
      ContinuousOn
        (fun x : ℝ =>
          (Complex.dampedQuadraticDerivativeDenominator
            epsilon frequency x) ^ 2)
        set :=
    (Complex.continuous_dampedQuadraticDerivativeDenominator
      epsilon frequency).continuousOn.pow 2
  have hdenominator_ne :
      ∀ x ∈ set,
        (Complex.dampedQuadraticDerivativeDenominator
          epsilon frequency x) ^ 2 ≠ 0 :=
    fun x hx =>
      pow_ne_zero 2
        (Complex.dampedQuadraticDerivativeDenominator_ne_zero
          epsilon frequency x hfrequency (hset x hx))
  exact hnumerator.div hdenominator hdenominator_ne

/-- Exact integration-by-parts identity for a damped quadratic tail.  All
hypotheses needed for calculus are discharged from the positive near
endpoint and nonzero oscillatory frequency. -/
theorem Complex.intervalIntegral_dampedQuadraticOscillator_eq_boundary_sub_remainder
    (epsilon frequency left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    (∫ x in left..right,
        Complex.dampedQuadraticOscillator epsilon frequency x) =
      Complex.dampedQuadraticIntegrationCoefficient
          epsilon frequency right *
          Complex.dampedQuadraticOscillator epsilon frequency right -
        Complex.dampedQuadraticIntegrationCoefficient
          epsilon frequency left *
          Complex.dampedQuadraticOscillator epsilon frequency left -
        ∫ x in left..right,
          Complex.dampedQuadraticIntegrationCoefficientDerivative
              epsilon frequency x *
            Complex.dampedQuadraticOscillator epsilon frequency x := by
  have hset : ∀ x ∈ Set.uIcc left right, x ≠ 0 :=
    fun x hx => by
      have hxIcc : x ∈ Set.Icc left right :=
        Eq.subst
          (motive := fun set : Set ℝ => x ∈ set)
          (Set.uIcc_of_le hleft_right)
          hx
      exact Real.ne_zero_of_mem_Icc_of_pos_left hleft hxIcc
  have hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.dampedQuadraticIntegrationCoefficient epsilon frequency)
          (Complex.dampedQuadraticIntegrationCoefficientDerivative
            epsilon frequency x)
          x :=
    fun x hx =>
      Complex.hasDerivAt_dampedQuadraticIntegrationCoefficient_named
        epsilon frequency x hfrequency (hset x hx)
  have hoscillator :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.dampedQuadraticOscillator epsilon frequency)
          (Complex.dampedQuadraticOscillatorDerivative epsilon frequency x)
          x :=
    fun x _hx =>
      Complex.hasDerivAt_dampedQuadraticOscillator_named
        epsilon frequency x
  have hcoefficientDerivative_integrable :
      IntervalIntegrable
        (Complex.dampedQuadraticIntegrationCoefficientDerivative
          epsilon frequency)
        volume left right :=
    (Complex.continuousOn_dampedQuadraticIntegrationCoefficientDerivative
      epsilon frequency hfrequency (Set.uIcc left right) hset).intervalIntegrable
  have hoscillatorDerivative_integrable :
      IntervalIntegrable
        (Complex.dampedQuadraticOscillatorDerivative epsilon frequency)
        volume left right :=
    (Complex.continuous_dampedQuadraticOscillatorDerivative
      epsilon frequency).intervalIntegrable left right
  have hcancellation :
      ∀ x ∈ [[left, right]],
        Complex.dampedQuadraticIntegrationCoefficient epsilon frequency x *
            Complex.dampedQuadraticOscillatorDerivative epsilon frequency x =
          Complex.dampedQuadraticOscillator epsilon frequency x :=
    fun x hx =>
      Complex.dampedQuadraticIntegrationCoefficient_mul_deriv
        epsilon frequency x hfrequency (hset x hx)
  exact
    Complex.intervalIntegral_oscillator_eq_boundary_sub_remainder
      (Complex.dampedQuadraticOscillator epsilon frequency)
      (Complex.dampedQuadraticIntegrationCoefficient epsilon frequency)
      (Complex.dampedQuadraticOscillatorDerivative epsilon frequency)
      (Complex.dampedQuadraticIntegrationCoefficientDerivative
        epsilon frequency)
      left right hcoefficient hoscillator
      hcoefficientDerivative_integrable
      hoscillatorDerivative_integrable hcancellation

/-- The damped real quadratic phase has quadratic coefficient in the open
left half-plane. -/
theorem Complex.dampedQuadraticCoefficient_re_neg
    (epsilon frequency : ℝ)
    (hepsilon : 0 < epsilon) :
    ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ))).re < 0 := by
  exact
    Eq.subst
      (motive := fun r : ℝ => r < 0)
      (Complex.dampedQuadraticCoefficient_re epsilon frequency).symm
      (neg_lt_zero.mpr hepsilon)

/-- A damped quadratic coefficient is nonzero. -/
theorem Complex.dampedQuadraticCoefficient_ne_zero
    (epsilon frequency : ℝ)
    (hepsilon : 0 < epsilon) :
    (-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) ≠ 0 := by
  intro hzero
  have hre_zero :
      ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ))).re = 0 :=
    congrArg Complex.re hzero
  have hneg_zero : -epsilon = 0 :=
    Eq.trans
      (Complex.dampedQuadraticCoefficient_re epsilon frequency).symm
      hre_zero
  have hepsilon_zero : epsilon = 0 :=
    neg_eq_zero.mp hneg_zero
  exact ne_of_gt hepsilon hepsilon_zero

/-- Pointwise norm of the damped quadratic oscillation. -/
theorem Complex.norm_exp_dampedQuadratic
    (epsilon frequency x : ℝ) :
    ‖Complex.exp
        ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) * (x : ℂ) ^ 2)‖ =
      Real.exp (-epsilon * x ^ 2) := by
  have hsquare : ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) :=
    (Complex.ofReal_pow x 2).symm
  have hsquare_re : ((x : ℂ) ^ 2).re = x ^ 2 := by
    exact
      Eq.trans
        (congrArg Complex.re hsquare)
        (Complex.ofReal_re (x ^ 2))
  have hsquare_im : ((x : ℂ) ^ 2).im = 0 := by
    exact
      Eq.trans
        (congrArg Complex.im hsquare)
        (Complex.ofReal_im (x ^ 2))
  have hexponent_re :
      (((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
        (x : ℂ) ^ 2)).re = -epsilon * x ^ 2 := by
    exact
      Eq.trans
        (Complex.mul_re
          (-(epsilon : ℂ) + Complex.I * (frequency : ℂ))
          ((x : ℂ) ^ 2))
        (Eq.trans
          (congrArg
            (fun r : ℝ =>
              r * ((x : ℂ) ^ 2).re -
                (-(epsilon : ℂ) + Complex.I * (frequency : ℂ)).im *
                  ((x : ℂ) ^ 2).im)
            (Complex.dampedQuadraticCoefficient_re epsilon frequency))
          (Eq.trans
            (congrArg
              (fun r : ℝ =>
                -epsilon * r -
                  (-(epsilon : ℂ) + Complex.I * (frequency : ℂ)).im *
                    ((x : ℂ) ^ 2).im)
              hsquare_re)
            (Eq.trans
              (congrArg
                (fun r : ℝ =>
                  -epsilon * x ^ 2 -
                    (-(epsilon : ℂ) + Complex.I * (frequency : ℂ)).im * r)
                hsquare_im)
              (Eq.trans
                (congrArg
                  (fun value : ℝ => -epsilon * x ^ 2 - value)
                  (mul_zero
                    (-(epsilon : ℂ) +
                      Complex.I * (frequency : ℂ)).im))
                (sub_zero (-epsilon * x ^ 2))))))
  exact
    Eq.trans
      (Complex.norm_eq_abs
        (Complex.exp
          ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
            (x : ℂ) ^ 2)))
      (Eq.trans
        (Complex.abs_exp
          ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
            (x : ℂ) ^ 2))
        (congrArg Real.exp hexponent_re))

/-- Named pointwise norm formula for the damped quadratic oscillator. -/
theorem Complex.norm_dampedQuadraticOscillator
    (epsilon frequency x : ℝ) :
    ‖Complex.dampedQuadraticOscillator epsilon frequency x‖ =
      Real.exp (-epsilon * x ^ 2) :=
  Complex.norm_exp_dampedQuadratic epsilon frequency x

/-- Nonnegative Gaussian damping makes the oscillator uniformly bounded by
one. -/
theorem Complex.norm_dampedQuadraticOscillator_le_one
    (epsilon frequency x : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    ‖Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤ 1 := by
  have hexponent_nonpos : -epsilon * x ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hepsilon)
      (sq_nonneg x)
  have hexp_le : Real.exp (-epsilon * x ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr hexponent_nonpos
  exact
    Eq.subst
      (motive := fun value : ℝ => value ≤ 1)
      (Complex.norm_dampedQuadraticOscillator epsilon frequency x).symm
      hexp_le

/-- Exact norm of the damped quadratic derivative denominator. -/
theorem Complex.norm_dampedQuadraticDerivativeDenominator
    (epsilon frequency x : ℝ) :
    ‖Complex.dampedQuadraticDerivativeDenominator epsilon frequency x‖ =
      2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ * ‖x‖ := by
  have houter :
      ‖2 * Complex.dampedQuadraticCoefficient epsilon frequency * (x : ℂ)‖ =
        ‖2 * Complex.dampedQuadraticCoefficient epsilon frequency‖ *
          ‖(x : ℂ)‖ :=
    norm_mul
      (2 * Complex.dampedQuadraticCoefficient epsilon frequency)
      (x : ℂ)
  have hinner :
      ‖2 * Complex.dampedQuadraticCoefficient epsilon frequency‖ =
        ‖(2 : ℂ)‖ *
          ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ :=
    norm_mul (2 : ℂ)
      (Complex.dampedQuadraticCoefficient epsilon frequency)
  have htwo : ‖(2 : ℂ)‖ = 2 :=
    Complex.norm_ofNat 2
  have hx : ‖(x : ℂ)‖ = ‖x‖ :=
    Complex.norm_real x
  have hinner_normalized :
      ‖2 * Complex.dampedQuadraticCoefficient epsilon frequency‖ =
        2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ :=
    hinner.trans
      (congrArg₂ (fun u v : ℝ => u * v) htwo rfl)
  exact
    houter.trans
      (congrArg₂ (fun u v : ℝ => u * v)
        hinner_normalized hx)

/-- Exact norm of the reciprocal damped integration coefficient. -/
theorem Complex.norm_dampedQuadraticIntegrationCoefficient
    (epsilon frequency x : ℝ) :
    ‖Complex.dampedQuadraticIntegrationCoefficient epsilon frequency x‖ =
      (2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ * ‖x‖)⁻¹ := by
  have hinverse :
      ‖(Complex.dampedQuadraticDerivativeDenominator
          epsilon frequency x)⁻¹‖ =
        ‖Complex.dampedQuadraticDerivativeDenominator
          epsilon frequency x‖⁻¹ :=
    norm_inv
      (Complex.dampedQuadraticDerivativeDenominator epsilon frequency x)
  exact
    hinverse.trans
      (congrArg Inv.inv
        (Complex.norm_dampedQuadraticDerivativeDenominator
          epsilon frequency x))

/-- Uniform reciprocal-coefficient bound controlled only by the oscillatory
frequency and the positive endpoint. -/
theorem Complex.norm_dampedQuadraticIntegrationCoefficient_le_frequency
    (epsilon frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : 0 < x) :
    ‖Complex.dampedQuadraticIntegrationCoefficient epsilon frequency x‖ ≤
      (2 * ‖frequency‖ * x)⁻¹ := by
  have hfrequency_norm_pos : 0 < ‖frequency‖ :=
    norm_pos_iff.mpr hfrequency
  have hx_norm : ‖x‖ = x :=
    Real.norm_of_nonneg (le_of_lt hx)
  have hcoefficient_bound :
      ‖frequency‖ ≤
        ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ :=
    Complex.norm_frequency_le_norm_dampedQuadraticCoefficient
      epsilon frequency
  have htwo_nonneg : 0 ≤ (2 : ℝ) :=
    le_of_lt zero_lt_two
  have hscaled :
      2 * ‖frequency‖ ≤
        2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ :=
    mul_le_mul_of_nonneg_left hcoefficient_bound htwo_nonneg
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hproduct :
      2 * ‖frequency‖ * x ≤
        2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ * x :=
    mul_le_mul_of_nonneg_right hscaled hx_nonneg
  have hlower_pos : 0 < 2 * ‖frequency‖ * x :=
    mul_pos
      (mul_pos zero_lt_two hfrequency_norm_pos)
      hx
  have hinverse :
      (2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ * x)⁻¹ ≤
        (2 * ‖frequency‖ * x)⁻¹ :=
    inv_anti₀ hlower_pos hproduct
  have hnorm_exact :=
    Complex.norm_dampedQuadraticIntegrationCoefficient
      epsilon frequency x
  have hnormalized :
      ‖Complex.dampedQuadraticIntegrationCoefficient epsilon frequency x‖ =
        (2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ * x)⁻¹ :=
    hnorm_exact.trans
      (congrArg Inv.inv
        (congrArg
          (fun value : ℝ =>
            2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ * value)
          hx_norm))
  exact
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ (2 * ‖frequency‖ * x)⁻¹)
      hnormalized.symm
      hinverse

/-- Exact norm of the reciprocal damped-coefficient derivative. -/
theorem Complex.norm_dampedQuadraticIntegrationCoefficientDerivative
    (epsilon frequency x : ℝ) :
    ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
        epsilon frequency x‖ =
      (2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖) /
        (2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ *
          ‖x‖) ^ 2 := by
  let coefficient : ℂ :=
    Complex.dampedQuadraticCoefficient epsilon frequency
  have hdivision :
      ‖-(2 * coefficient) /
          (Complex.dampedQuadraticDerivativeDenominator
            epsilon frequency x) ^ 2‖ =
        ‖-(2 * coefficient)‖ /
          ‖(Complex.dampedQuadraticDerivativeDenominator
            epsilon frequency x) ^ 2‖ :=
    norm_div
      (-(2 * coefficient))
      ((Complex.dampedQuadraticDerivativeDenominator
        epsilon frequency x) ^ 2)
  have hnumerator_neg : ‖-(2 * coefficient)‖ = ‖2 * coefficient‖ :=
    norm_neg (2 * coefficient)
  have hnumerator_product :
      ‖2 * coefficient‖ = ‖(2 : ℂ)‖ * ‖coefficient‖ :=
    norm_mul (2 : ℂ) coefficient
  have hnumerator :
      ‖2 * coefficient‖ = 2 * ‖coefficient‖ :=
    hnumerator_product.trans
      (congrArg₂ (fun u v : ℝ => u * v)
        (Complex.norm_ofNat 2) rfl)
  have hdenominator_pow :
      ‖(Complex.dampedQuadraticDerivativeDenominator
          epsilon frequency x) ^ 2‖ =
        ‖Complex.dampedQuadraticDerivativeDenominator
          epsilon frequency x‖ ^ 2 :=
    norm_pow
      (Complex.dampedQuadraticDerivativeDenominator epsilon frequency x)
      2
  have hdenominator :
      ‖(Complex.dampedQuadraticDerivativeDenominator
          epsilon frequency x) ^ 2‖ =
        (2 * ‖coefficient‖ * ‖x‖) ^ 2 :=
    hdenominator_pow.trans
      (congrArg (fun value : ℝ => value ^ 2)
        (Complex.norm_dampedQuadraticDerivativeDenominator
          epsilon frequency x))
  exact
    hdivision.trans
      (congrArg₂ (fun numerator denominator : ℝ =>
        numerator / denominator)
        (hnumerator_neg.trans hnumerator)
        hdenominator)

/-- On a positive tail, the derivative norm is an exact inverse-square
density with damped scale. -/
theorem Complex.norm_dampedQuadraticIntegrationCoefficientDerivative_eq_invSquare
    (epsilon frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : 0 < x) :
    ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
        epsilon frequency x‖ =
      (2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖)⁻¹ *
        (x ^ 2)⁻¹ := by
  let scale : ℝ :=
    2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖
  have hcoefficient_ne :
      Complex.dampedQuadraticCoefficient epsilon frequency ≠ 0 :=
    Complex.dampedQuadraticCoefficient_ne_zero_of_frequency_ne_zero
      epsilon frequency hfrequency
  have hcoefficient_norm_pos :
      0 < ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ :=
    norm_pos_iff.mpr hcoefficient_ne
  have hscale_pos : 0 < scale :=
    mul_pos zero_lt_two hcoefficient_norm_pos
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  have hx_norm : ‖x‖ = x :=
    Real.norm_of_nonneg (le_of_lt hx)
  have hraw :
      ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
          epsilon frequency x‖ =
        scale / (scale * x) ^ 2 :=
    (Complex.norm_dampedQuadraticIntegrationCoefficientDerivative
      epsilon frequency x).trans
      (congrArg
        (fun coordinate : ℝ => scale / (scale * coordinate) ^ 2)
        hx_norm)
  exact
    hraw.trans
      (Real.div_mul_square_eq_inv_mul_square_inv scale x hscale_ne)

/-- Uniform inverse-square derivative bound controlled only by the real
oscillatory frequency. -/
theorem Complex.norm_dampedQuadraticIntegrationCoefficientDerivative_le_frequency
    (epsilon frequency x : ℝ)
    (hfrequency : frequency ≠ 0)
    (hx : 0 < x) :
    ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
        epsilon frequency x‖ ≤
      (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹ := by
  have hexact :=
    Complex.norm_dampedQuadraticIntegrationCoefficientDerivative_eq_invSquare
      epsilon frequency x hfrequency hx
  have hfrequency_norm_pos : 0 < ‖frequency‖ :=
    norm_pos_iff.mpr hfrequency
  have hfrequency_scale_pos : 0 < 2 * ‖frequency‖ :=
    mul_pos zero_lt_two hfrequency_norm_pos
  have hcoefficient_bound :
      ‖frequency‖ ≤
        ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ :=
    Complex.norm_frequency_le_norm_dampedQuadraticCoefficient
      epsilon frequency
  have hscale_bound :
      2 * ‖frequency‖ ≤
        2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖ :=
    mul_le_mul_of_nonneg_left hcoefficient_bound
      (le_of_lt zero_lt_two)
  have hinverse_bound :
      (2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖)⁻¹ ≤
        (2 * ‖frequency‖)⁻¹ :=
    inv_anti₀ hfrequency_scale_pos hscale_bound
  have hx_density_nonneg : 0 ≤ (x ^ 2)⁻¹ :=
    inv_nonneg.mpr (sq_nonneg x)
  have hproduct :
      (2 * ‖Complex.dampedQuadraticCoefficient epsilon frequency‖)⁻¹ *
          (x ^ 2)⁻¹ ≤
        (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right hinverse_bound hx_density_nonneg
  exact
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹)
      hexact.symm
      hproduct

/-- Norm form of the damped quadratic integration-by-parts identity. -/
theorem Complex.norm_intervalIntegral_dampedQuadraticOscillator_le_boundary_add_remainder
    (epsilon frequency left right : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
        Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤
      ‖Complex.dampedQuadraticIntegrationCoefficient
          epsilon frequency right‖ +
        ‖Complex.dampedQuadraticIntegrationCoefficient
          epsilon frequency left‖ +
        ∫ x in left..right,
          ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
            epsilon frequency x‖ := by
  have hidentity :=
    Complex.intervalIntegral_dampedQuadraticOscillator_eq_boundary_sub_remainder
      epsilon frequency left right hfrequency hleft hleft_right
  let rightBoundary : ℂ :=
    Complex.dampedQuadraticIntegrationCoefficient epsilon frequency right *
      Complex.dampedQuadraticOscillator epsilon frequency right
  let leftBoundary : ℂ :=
    Complex.dampedQuadraticIntegrationCoefficient epsilon frequency left *
      Complex.dampedQuadraticOscillator epsilon frequency left
  let remainder : ℂ :=
    ∫ x in left..right,
      Complex.dampedQuadraticIntegrationCoefficientDerivative
          epsilon frequency x *
        Complex.dampedQuadraticOscillator epsilon frequency x
  have htriangle :
      ‖rightBoundary - leftBoundary - remainder‖ ≤
        ‖rightBoundary‖ + ‖leftBoundary‖ + ‖remainder‖ := by
    exact le_trans
      (norm_sub_le (rightBoundary - leftBoundary) remainder)
      (add_le_add_right
        (norm_sub_le rightBoundary leftBoundary)
        ‖remainder‖)
  have hright :
      ‖rightBoundary‖ ≤
        ‖Complex.dampedQuadraticIntegrationCoefficient
          epsilon frequency right‖ := by
    have hnorm :=
      norm_mul
        (Complex.dampedQuadraticIntegrationCoefficient
          epsilon frequency right)
        (Complex.dampedQuadraticOscillator epsilon frequency right)
    have hoscillator :=
      Complex.norm_dampedQuadraticOscillator_le_one
        epsilon frequency right hepsilon
    have hmul :
        ‖Complex.dampedQuadraticIntegrationCoefficient
            epsilon frequency right‖ *
            ‖Complex.dampedQuadraticOscillator epsilon frequency right‖ ≤
          ‖Complex.dampedQuadraticIntegrationCoefficient
            epsilon frequency right‖ * 1 :=
      mul_le_mul_of_nonneg_left hoscillator
        (norm_nonneg
          (Complex.dampedQuadraticIntegrationCoefficient
            epsilon frequency right))
    exact
      Eq.subst
        (motive := fun value : ℝ =>
          value ≤
            ‖Complex.dampedQuadraticIntegrationCoefficient
              epsilon frequency right‖)
        hnorm.symm
        (le_trans hmul
          (le_of_eq
            (mul_one
              ‖Complex.dampedQuadraticIntegrationCoefficient
                epsilon frequency right‖)))
  have hleft_boundary :
      ‖leftBoundary‖ ≤
        ‖Complex.dampedQuadraticIntegrationCoefficient
          epsilon frequency left‖ := by
    have hnorm :=
      norm_mul
        (Complex.dampedQuadraticIntegrationCoefficient
          epsilon frequency left)
        (Complex.dampedQuadraticOscillator epsilon frequency left)
    have hoscillator :=
      Complex.norm_dampedQuadraticOscillator_le_one
        epsilon frequency left hepsilon
    have hmul :
        ‖Complex.dampedQuadraticIntegrationCoefficient
            epsilon frequency left‖ *
            ‖Complex.dampedQuadraticOscillator epsilon frequency left‖ ≤
          ‖Complex.dampedQuadraticIntegrationCoefficient
            epsilon frequency left‖ * 1 :=
      mul_le_mul_of_nonneg_left hoscillator
        (norm_nonneg
          (Complex.dampedQuadraticIntegrationCoefficient
            epsilon frequency left))
    exact
      Eq.subst
        (motive := fun value : ℝ =>
          value ≤
            ‖Complex.dampedQuadraticIntegrationCoefficient
              epsilon frequency left‖)
        hnorm.symm
        (le_trans hmul
          (le_of_eq
            (mul_one
              ‖Complex.dampedQuadraticIntegrationCoefficient
                epsilon frequency left‖)))
  have hset : ∀ x ∈ Set.Icc left right, x ≠ 0 :=
    fun x hx =>
      Real.ne_zero_of_mem_Icc_of_pos_left
        hleft hx
  have hcoefficientDerivative_continuous :
      ContinuousOn
        (Complex.dampedQuadraticIntegrationCoefficientDerivative
          epsilon frequency)
        (Set.Icc left right) :=
    Complex.continuousOn_dampedQuadraticIntegrationCoefficientDerivative
      epsilon frequency hfrequency (Set.Icc left right) hset
  have hproduct_continuous :
      ContinuousOn
        (fun x : ℝ =>
          Complex.dampedQuadraticIntegrationCoefficientDerivative
              epsilon frequency x *
            Complex.dampedQuadraticOscillator epsilon frequency x)
        (Set.Icc left right) :=
    hcoefficientDerivative_continuous.mul
      (Complex.continuous_dampedQuadraticOscillator
        epsilon frequency).continuousOn
  have hproduct_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
              epsilon frequency x *
            Complex.dampedQuadraticOscillator epsilon frequency x‖)
        volume left right :=
    hproduct_continuous.norm.intervalIntegrable_of_Icc hleft_right
  have hcoefficientDerivative_norm_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
            epsilon frequency x‖)
        volume left right :=
    hcoefficientDerivative_continuous.norm.intervalIntegrable_of_Icc hleft_right
  have hremainder_norm :
      ‖remainder‖ ≤
        ∫ x in left..right,
          ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
            epsilon frequency x‖ := by
    have hintegral_norm :
        ‖remainder‖ ≤
          ∫ x in left..right,
            ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
                epsilon frequency x *
              Complex.dampedQuadraticOscillator epsilon frequency x‖ :=
      intervalIntegral.norm_integral_le_integral_norm
        hleft_right
        (f := fun x : ℝ =>
          Complex.dampedQuadraticIntegrationCoefficientDerivative
              epsilon frequency x *
            Complex.dampedQuadraticOscillator epsilon frequency x)
    have hpointwise :
        ∀ x ∈ Set.Icc left right,
          ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
                epsilon frequency x *
              Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤
            ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
              epsilon frequency x‖ := by
      intro x _hx
      have hnorm :=
        norm_mul
          (Complex.dampedQuadraticIntegrationCoefficientDerivative
            epsilon frequency x)
          (Complex.dampedQuadraticOscillator epsilon frequency x)
      have hoscillator :=
        Complex.norm_dampedQuadraticOscillator_le_one
          epsilon frequency x hepsilon
      have hmul :=
        mul_le_mul_of_nonneg_left hoscillator
          (norm_nonneg
            (Complex.dampedQuadraticIntegrationCoefficientDerivative
              epsilon frequency x))
      exact
        Eq.subst
          (motive := fun value : ℝ =>
            value ≤
              ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
                epsilon frequency x‖)
          hnorm.symm
          (le_trans hmul
            (le_of_eq
              (mul_one
                ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
                  epsilon frequency x‖)))
    have hintegral_mono :=
      intervalIntegral.integral_mono_on
        hleft_right hproduct_integrable
        hcoefficientDerivative_norm_integrable hpointwise
    exact le_trans hintegral_norm hintegral_mono
  have hbounds :
      ‖rightBoundary‖ + ‖leftBoundary‖ + ‖remainder‖ ≤
        ‖Complex.dampedQuadraticIntegrationCoefficient
            epsilon frequency right‖ +
          ‖Complex.dampedQuadraticIntegrationCoefficient
            epsilon frequency left‖ +
          ∫ x in left..right,
            ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
              epsilon frequency x‖ :=
    add_le_add (add_le_add hright hleft_boundary) hremainder_norm
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          ‖Complex.dampedQuadraticIntegrationCoefficient
              epsilon frequency right‖ +
            ‖Complex.dampedQuadraticIntegrationCoefficient
              epsilon frequency left‖ +
            ∫ x in left..right,
              ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
                epsilon frequency x‖)
      hidentity.symm
      (le_trans htriangle hbounds)

/-- Uniform integral bound for the reciprocal-coefficient variation on a
positive damped quadratic tail. -/
theorem Complex.intervalIntegral_norm_dampedQuadraticIntegrationCoefficientDerivative_le_frequency
    (epsilon frequency left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    (∫ x in left..right,
        ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
          epsilon frequency x‖) ≤
      (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹) := by
  have hset : ∀ x ∈ Set.Icc left right, x ≠ 0 :=
    fun x hx =>
      Real.ne_zero_of_mem_Icc_of_pos_left
        hleft hx
  have hleft_function_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
            epsilon frequency x‖)
        volume left right :=
    (Complex.continuousOn_dampedQuadraticIntegrationCoefficientDerivative
      epsilon frequency hfrequency (Set.Icc left right) hset).norm.intervalIntegrable_of_Icc
        hleft_right
  have hsquare_continuous :
      ContinuousOn (fun x : ℝ => x ^ 2) (Set.Icc left right) :=
    continuousOn_id.pow 2
  have hsquare_ne :
      ∀ x ∈ Set.Icc left right, x ^ 2 ≠ 0 :=
    fun x hx => pow_ne_zero 2 (hset x hx)
  have hinverse_square_continuous :
      ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Icc left right) :=
    hsquare_continuous.inv₀ hsquare_ne
  have hright_function_integrable :
      IntervalIntegrable
        (fun x : ℝ => (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹)
        volume left right :=
    (continuousOn_const.mul hinverse_square_continuous).intervalIntegrable_of_Icc
      hleft_right
  have hpointwise :
      ∀ x ∈ Set.Icc left right,
        ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
            epsilon frequency x‖ ≤
          (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹ := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le hleft hx.1
    exact
      Complex.norm_dampedQuadraticIntegrationCoefficientDerivative_le_frequency
        epsilon frequency x hfrequency hx_pos
  have hintegral_mono :
      (∫ x in left..right,
          ‖Complex.dampedQuadraticIntegrationCoefficientDerivative
            epsilon frequency x‖) ≤
        ∫ x in left..right,
          (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹ :=
    intervalIntegral.integral_mono_on
      hleft_right hleft_function_integrable
      hright_function_integrable hpointwise
  have hconstant_out :
      (∫ x in left..right,
          (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹) =
        (2 * ‖frequency‖)⁻¹ *
          ∫ x in left..right, (x ^ 2)⁻¹ :=
    intervalIntegral.integral_const_mul
      (2 * ‖frequency‖)⁻¹
      (fun x : ℝ => (x ^ 2)⁻¹)
  have hintegral_exact :
      (∫ x in left..right,
          (2 * ‖frequency‖)⁻¹ * (x ^ 2)⁻¹) =
        (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹) :=
    hconstant_out.trans
      (congrArg
        (fun value : ℝ => (2 * ‖frequency‖)⁻¹ * value)
        (Real.intervalIntegral_square_inv
          left right hleft hleft_right))
  exact le_trans hintegral_mono (le_of_eq hintegral_exact)

/-- Uniform positive damped-tail estimate.  Its right-hand side is independent
of the damping parameter. -/
theorem Complex.norm_intervalIntegral_dampedQuadraticOscillator_le_uniform_tail
    (epsilon frequency left right : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
        Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤
      (2 * ‖frequency‖ * right)⁻¹ +
        (2 * ‖frequency‖ * left)⁻¹ +
        (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹) := by
  have hstructural :=
    Complex.norm_intervalIntegral_dampedQuadraticOscillator_le_boundary_add_remainder
      epsilon frequency left right hepsilon hfrequency hleft hleft_right
  have hright_pos : 0 < right := lt_of_lt_of_le hleft hleft_right
  have hright_bound :=
    Complex.norm_dampedQuadraticIntegrationCoefficient_le_frequency
      epsilon frequency right hfrequency hright_pos
  have hleft_bound :=
    Complex.norm_dampedQuadraticIntegrationCoefficient_le_frequency
      epsilon frequency left hfrequency hleft
  have hremainder_bound :=
    Complex.intervalIntegral_norm_dampedQuadraticIntegrationCoefficientDerivative_le_frequency
      epsilon frequency left right hfrequency hleft hleft_right
  have hcombined :=
    add_le_add (add_le_add hright_bound hleft_bound) hremainder_bound
  exact le_trans hstructural hcombined

/-- The damped quadratic oscillator is even. -/
theorem Complex.dampedQuadraticOscillator_neg
    (epsilon frequency x : ℝ) :
    Complex.dampedQuadraticOscillator epsilon frequency (-x) =
      Complex.dampedQuadraticOscillator epsilon frequency x := by
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
          Complex.dampedQuadraticCoefficient epsilon frequency * square)
        hsquare)

/-- Reflection identifies negative and positive damped quadratic tails. -/
theorem Complex.intervalIntegral_dampedQuadraticOscillator_neg_reflection
    (epsilon frequency left right : ℝ) :
    (∫ x in -right..-left,
        Complex.dampedQuadraticOscillator epsilon frequency x) =
      ∫ x in left..right,
        Complex.dampedQuadraticOscillator epsilon frequency x := by
  have hreflection :
      (∫ x in left..right,
          Complex.dampedQuadraticOscillator epsilon frequency (-x)) =
        ∫ x in -right..-left,
          Complex.dampedQuadraticOscillator epsilon frequency x :=
    intervalIntegral.integral_comp_neg
      (f := Complex.dampedQuadraticOscillator epsilon frequency)
      (a := left) (b := right)
  have heven :
      (∫ x in left..right,
          Complex.dampedQuadraticOscillator epsilon frequency (-x)) =
        ∫ x in left..right,
          Complex.dampedQuadraticOscillator epsilon frequency x :=
    intervalIntegral.integral_congr
      (fun x _hx =>
        Complex.dampedQuadraticOscillator_neg epsilon frequency x)
  exact hreflection.symm.trans heven

/-- Uniform negative damped-tail estimate obtained by reflection. -/
theorem Complex.norm_intervalIntegral_dampedQuadraticOscillator_negativeTail_le_uniform_tail
    (epsilon frequency left right : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in -right..-left,
        Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤
      (2 * ‖frequency‖ * right)⁻¹ +
        (2 * ‖frequency‖ * left)⁻¹ +
        (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹) := by
  have hpositive :=
    Complex.norm_intervalIntegral_dampedQuadraticOscillator_le_uniform_tail
      epsilon frequency left right hepsilon hfrequency hleft hleft_right
  have hreflection :=
    Complex.intervalIntegral_dampedQuadraticOscillator_neg_reflection
      epsilon frequency left right
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          (2 * ‖frequency‖ * right)⁻¹ +
            (2 * ‖frequency‖ * left)⁻¹ +
            (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹))
      hreflection.symm
      hpositive

/-- Product-inverse normalization for the uniform damped boundary term. -/
theorem Real.dampedQuadratic_boundaryInv_eq_scaleInv_mul_endpointInv
    (frequency endpoint : ℝ) :
    (2 * ‖frequency‖ * endpoint)⁻¹ =
      (2 * ‖frequency‖)⁻¹ * endpoint⁻¹ := by
  have hreverse :
      (2 * ‖frequency‖ * endpoint)⁻¹ =
        endpoint⁻¹ * (2 * ‖frequency‖)⁻¹ :=
    mul_inv_rev (2 * ‖frequency‖) endpoint
  exact hreverse.trans
    (mul_comm endpoint⁻¹ (2 * ‖frequency‖)⁻¹)

/-- Simplified uniform damped-tail estimate depending only on the near
endpoint. -/
theorem Complex.norm_intervalIntegral_dampedQuadraticOscillator_le_two_nearEndpoint
    (epsilon frequency left right : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
        Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤
      ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹ := by
  have hraw :=
    Complex.norm_intervalIntegral_dampedQuadraticOscillator_le_uniform_tail
      epsilon frequency left right hepsilon hfrequency hleft hleft_right
  have hright_normalized :=
    Real.dampedQuadratic_boundaryInv_eq_scaleInv_mul_endpointInv
      frequency right
  have hleft_normalized :=
    Real.dampedQuadratic_boundaryInv_eq_scaleInv_mul_endpointInv
      frequency left
  have hbudget :
      (2 * ‖frequency‖ * right)⁻¹ +
          (2 * ‖frequency‖ * left)⁻¹ +
          (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹) =
        ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹ := by
    exact
      (congrArg₂
        (fun rightTerm leftTerm : ℝ =>
          rightTerm + leftTerm +
            (2 * ‖frequency‖)⁻¹ * (left⁻¹ - right⁻¹))
        hright_normalized hleft_normalized).trans
        (Real.quadraticTail_budget_eq_two_leftEndpoint
          (2 * ‖frequency‖)⁻¹ left⁻¹ right⁻¹)
  exact le_trans hraw (le_of_eq hbudget)

/-- Simplified reflected negative damped-tail estimate. -/
theorem Complex.norm_intervalIntegral_dampedQuadraticOscillator_negativeTail_le_two_nearEndpoint
    (epsilon frequency left right : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in -right..-left,
        Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤
      ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹ := by
  have hpositive :=
    Complex.norm_intervalIntegral_dampedQuadraticOscillator_le_two_nearEndpoint
      epsilon frequency left right hepsilon hfrequency hleft hleft_right
  have hreflection :=
    Complex.intervalIntegral_dampedQuadraticOscillator_neg_reflection
      epsilon frequency left right
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹)
      hreflection.symm
      hpositive

/-- Exact whole-line integral of a damped quadratic oscillation. -/
theorem Complex.integral_dampedQuadratic
    (epsilon frequency : ℝ)
    (hepsilon : 0 < epsilon) :
    (∫ x : ℝ,
      Complex.exp
        ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) * (x : ℂ) ^ 2)) =
      (Real.pi /
        -(-(epsilon : ℂ) + Complex.I * (frequency : ℂ))) ^
          (1 / 2 : ℂ) := by
  let coefficient : ℂ :=
    -(epsilon : ℂ) + Complex.I * (frequency : ℂ)
  have hraw :=
    integral_cexp_quadratic
      (Complex.dampedQuadraticCoefficient_re_neg
        epsilon frequency hepsilon)
      0 0
  have hexponent (x : ℝ) :
      coefficient * (x : ℂ) ^ 2 + 0 * (x : ℂ) + 0 =
        coefficient * (x : ℂ) ^ 2 := by
    exact
      Eq.trans
        (congrArg
          (fun value : ℂ => coefficient * (x : ℂ) ^ 2 + value + 0)
          (zero_mul (x : ℂ)))
        (Eq.trans
          (congrArg (fun value : ℂ => value + 0)
            (add_zero (coefficient * (x : ℂ) ^ 2)))
          (add_zero (coefficient * (x : ℂ) ^ 2)))
  have hleft :
      (∫ x : ℝ,
        Complex.exp
          (coefficient * (x : ℂ) ^ 2 + 0 * (x : ℂ) + 0)) =
        ∫ x : ℝ, Complex.exp (coefficient * (x : ℂ) ^ 2) :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall
        (fun x => congrArg Complex.exp (hexponent x)))
  have hright :
      (Real.pi / -coefficient) ^ (1 / 2 : ℂ) *
          Complex.exp (0 - 0 ^ 2 / (4 * coefficient)) =
        (Real.pi / -coefficient) ^ (1 / 2 : ℂ) := by
    have hzero_exponent :
        (0 : ℂ) - 0 ^ 2 / (4 * coefficient) = 0 := by
      exact
        Eq.trans
          (congrArg (fun value : ℂ => 0 - value / (4 * coefficient))
            (zero_pow (OfNat.ofNat_ne_zero 2)))
          (Eq.trans
            (congrArg (fun value : ℂ => 0 - value) (zero_div (4 * coefficient)))
            (sub_zero 0))
    exact
      Eq.trans
        (congrArg
          (fun value : ℂ =>
            (Real.pi / -coefficient) ^ (1 / 2 : ℂ) * Complex.exp value)
          hzero_exponent)
        (Eq.trans
          (congrArg
            (fun value : ℂ =>
              (Real.pi / -coefficient) ^ (1 / 2 : ℂ) * value)
            Complex.exp_zero)
          (mul_one ((Real.pi / -coefficient) ^ (1 / 2 : ℂ))))
  exact hleft.symm.trans (hraw.trans hright)

/-- The damped quadratic oscillation is integrable on the real line. -/
theorem Complex.integrable_dampedQuadratic
    (epsilon frequency : ℝ)
    (hepsilon : 0 < epsilon) :
    Integrable
      (fun x : ℝ =>
        Complex.exp
          ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) * (x : ℂ) ^ 2)) := by
  let coefficient : ℂ :=
    -(epsilon : ℂ) + Complex.I * (frequency : ℂ)
  have hraw :=
    integrable_cexp_quadratic'
      (Complex.dampedQuadraticCoefficient_re_neg
        epsilon frequency hepsilon)
      0 0
  exact
    hraw.congr
      (Filter.Eventually.of_forall
        (fun x => by
          exact congrArg Complex.exp
            (Eq.trans
              (congrArg
                (fun value : ℂ => coefficient * (x : ℂ) ^ 2 + value + 0)
                (zero_mul (x : ℂ)))
              (Eq.trans
                (congrArg (fun value : ℂ => value + 0)
                  (add_zero (coefficient * (x : ℂ) ^ 2)))
                (add_zero (coefficient * (x : ℂ) ^ 2))))))

/-- Named whole-line integrability of the damped quadratic oscillator. -/
theorem Complex.integrable_dampedQuadraticOscillator
    (epsilon frequency : ℝ)
    (hepsilon : 0 < epsilon) :
    Integrable
      (Complex.dampedQuadraticOscillator epsilon frequency) :=
  Complex.integrable_dampedQuadratic epsilon frequency hepsilon

/-- Uniform positive half-line tail estimate, obtained from the finite bound
by sending the far endpoint to infinity. -/
theorem Complex.norm_integral_Ioi_dampedQuadraticOscillator_le_two_nearEndpoint
    (epsilon frequency left : ℝ)
    (hepsilon : 0 < epsilon)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left) :
    ‖∫ x in Set.Ioi left,
        Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤
      ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹ := by
  have hintegrableOn :
      IntegrableOn
        (Complex.dampedQuadraticOscillator epsilon frequency)
        (Set.Ioi left) :=
    (Complex.integrable_dampedQuadraticOscillator
      epsilon frequency hepsilon).integrableOn
  have hlimit :
      Filter.Tendsto
        (fun right : ℝ =>
          ∫ x in left..right,
            Complex.dampedQuadraticOscillator epsilon frequency x)
        Filter.atTop
        (𝓝
          (∫ x in Set.Ioi left,
            Complex.dampedQuadraticOscillator epsilon frequency x)) :=
    intervalIntegral_tendsto_integral_Ioi
      left hintegrableOn Filter.tendsto_id
  have hnorm_limit :
      Filter.Tendsto
        (fun right : ℝ =>
          ‖∫ x in left..right,
            Complex.dampedQuadraticOscillator epsilon frequency x‖)
        Filter.atTop
        (𝓝
          ‖∫ x in Set.Ioi left,
            Complex.dampedQuadraticOscillator epsilon frequency x‖) :=
    tendsto_norm.comp hlimit
  have heventually :
      ∀ᶠ right : ℝ in Filter.atTop,
        ‖∫ x in left..right,
            Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤
          ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹ :=
    (Filter.eventually_ge_atTop left).mono
      (fun right hleft_right =>
        Complex.norm_intervalIntegral_dampedQuadraticOscillator_le_two_nearEndpoint
          epsilon frequency left right (le_of_lt hepsilon)
          hfrequency hleft hleft_right)
  exact le_of_tendsto hnorm_limit heventually

/-- Uniform negative half-line tail estimate by reflection. -/
theorem Complex.norm_integral_Iic_dampedQuadraticOscillator_le_two_nearEndpoint
    (epsilon frequency left : ℝ)
    (hepsilon : 0 < epsilon)
    (hfrequency : frequency ≠ 0)
    (hleft : 0 < left) :
    ‖∫ x in Set.Iic (-left),
        Complex.dampedQuadraticOscillator epsilon frequency x‖ ≤
      ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹ := by
  have hreflection :
      (∫ x in Set.Ioi left,
          Complex.dampedQuadraticOscillator epsilon frequency (-x)) =
        ∫ x in Set.Iic (-left),
          Complex.dampedQuadraticOscillator epsilon frequency x :=
    integral_comp_neg_Ioi left
      (Complex.dampedQuadraticOscillator epsilon frequency)
  have heven :
      (∫ x in Set.Ioi left,
          Complex.dampedQuadraticOscillator epsilon frequency (-x)) =
        ∫ x in Set.Ioi left,
          Complex.dampedQuadraticOscillator epsilon frequency x :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun x _hx =>
        Complex.dampedQuadraticOscillator_neg epsilon frequency x)
  have hequality :
      (∫ x in Set.Iic (-left),
          Complex.dampedQuadraticOscillator epsilon frequency x) =
        ∫ x in Set.Ioi left,
          Complex.dampedQuadraticOscillator epsilon frequency x :=
    hreflection.symm.trans heven
  have hpositive :=
    Complex.norm_integral_Ioi_dampedQuadraticOscillator_le_two_nearEndpoint
      epsilon frequency left hepsilon hfrequency hleft
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          ((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * left⁻¹)
      hequality.symm
      hpositive

/-- Exact whole-line decomposition into the symmetric middle interval and
the two exterior half-line tails. -/
theorem Complex.integral_dampedQuadraticOscillator_sub_symmetricInterval_eq_tails
    (epsilon frequency radius : ℝ)
    (hepsilon : 0 < epsilon)
    (hradius : 0 < radius) :
    (∫ x : ℝ,
        Complex.dampedQuadraticOscillator epsilon frequency x) -
      (∫ x in -radius..radius,
        Complex.dampedQuadraticOscillator epsilon frequency x) =
      (∫ x in Set.Iic (-radius),
          Complex.dampedQuadraticOscillator epsilon frequency x) +
        (∫ x in Set.Ioi radius,
          Complex.dampedQuadraticOscillator epsilon frequency x) := by
  let f : ℝ → ℂ :=
    Complex.dampedQuadraticOscillator epsilon frequency
  let negativeTail : Set ℝ := Set.Iic (-radius)
  let middle : Set ℝ := Set.Ioc (-radius) radius
  let positiveTail : Set ℝ := Set.Ioi radius
  have hf : Integrable f :=
    Complex.integrable_dampedQuadraticOscillator
      epsilon frequency hepsilon
  have hnegative_middle : Disjoint negativeTail middle := by
    exact Set.disjoint_left.mpr
      (fun x hxNegative hxMiddle =>
        have hxNegative_le : x ≤ -radius := hxNegative
        have hxMiddle_lt : -radius < x := hxMiddle.1
        (not_lt_of_ge hxNegative_le) hxMiddle_lt)
  have hnegativeMiddle_positive :
      Disjoint (negativeTail ∪ middle) positiveTail := by
    exact Set.disjoint_left.mpr
      (fun x hxUnion hxPositive =>
        match hxUnion with
        | Or.inl hxNegative =>
            have hx_le_neg : x ≤ -radius := hxNegative
            have hneg_lt_pos : -radius < radius := by
              exact lt_of_lt_of_le (neg_lt_zero.mpr hradius) (le_of_lt hradius)
            have hx_lt_radius : x < radius :=
              lt_of_le_of_lt hx_le_neg hneg_lt_pos
            (not_lt_of_ge (le_of_lt hxPositive)) hx_lt_radius
        | Or.inr hxMiddle =>
            (not_lt_of_ge hxMiddle.2) hxPositive)
  have hdomain :
      (negativeTail ∪ middle) ∪ positiveTail = Set.univ := by
    exact Set.eq_univ_of_forall
      (fun x => by
        match Classical.em (x ≤ -radius) with
        | Or.inl hxNegative =>
            exact Or.inl (Or.inl hxNegative)
        | Or.inr hxNotNegative =>
            match Classical.em (x ≤ radius) with
            | Or.inl hxMiddleRight =>
                exact Or.inl
                  (Or.inr
                    ⟨lt_of_not_ge hxNotNegative, hxMiddleRight⟩)
            | Or.inr hxNotMiddle =>
                exact Or.inr (lt_of_not_ge hxNotMiddle))
  have hintegral_negative_middle :
      (∫ x in negativeTail ∪ middle, f x) =
        (∫ x in negativeTail, f x) +
          ∫ x in middle, f x :=
    setIntegral_union hnegative_middle measurableSet_Ioc
      hf.integrableOn hf.integrableOn
  have hintegral_all :
      (∫ x in (negativeTail ∪ middle) ∪ positiveTail, f x) =
        (∫ x in negativeTail ∪ middle, f x) +
          ∫ x in positiveTail, f x :=
    setIntegral_union hnegativeMiddle_positive measurableSet_Ioi
      hf.integrableOn hf.integrableOn
  have hwhole :
      (∫ x : ℝ, f x) =
        ((∫ x in negativeTail, f x) +
          (∫ x in middle, f x)) +
            ∫ x in positiveTail, f x := by
    have hdomain_integral :
        (∫ x in (negativeTail ∪ middle) ∪ positiveTail, f x) =
          ∫ x : ℝ, f x :=
      (congrArg
        (fun set : Set ℝ => ∫ x in set, f x)
        hdomain).trans setIntegral_univ
    exact hdomain_integral.symm.trans
      (hintegral_all.trans
        (congrArg
          (fun value : ℂ => value + ∫ x in positiveTail, f x)
          hintegral_negative_middle))
  have hmiddle_interval :
      (∫ x in -radius..radius, f x) =
        ∫ x in middle, f x :=
    intervalIntegral.integral_of_le
      (le_trans (neg_nonpos.mpr (le_of_lt hradius)) (le_of_lt hradius))
  have hsubtract :=
    Complex.threePiece_sub_middle
      (∫ x : ℝ, f x)
      (∫ x in negativeTail, f x)
      (∫ x in middle, f x)
      (∫ x in positiveTail, f x)
      hwhole
  exact
    Eq.subst
      (motive := fun middleValue : ℂ =>
        (∫ x : ℝ, f x) - middleValue =
          (∫ x in negativeTail, f x) +
            ∫ x in positiveTail, f x)
      hmiddle_interval.symm
      hsubtract

/-- Uniform comparison between the whole-line damped integral and its
symmetric finite truncation. -/
theorem Complex.norm_integral_dampedQuadraticOscillator_sub_symmetricInterval_le
    (epsilon frequency radius : ℝ)
    (hepsilon : 0 < epsilon)
    (hfrequency : frequency ≠ 0)
    (hradius : 0 < radius) :
    ‖(∫ x : ℝ,
          Complex.dampedQuadraticOscillator epsilon frequency x) -
        (∫ x in -radius..radius,
          Complex.dampedQuadraticOscillator epsilon frequency x)‖ ≤
      (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * radius⁻¹) +
        (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * radius⁻¹) := by
  have hdecomposition :=
    Complex.integral_dampedQuadraticOscillator_sub_symmetricInterval_eq_tails
      epsilon frequency radius hepsilon hradius
  have hnegative :=
    Complex.norm_integral_Iic_dampedQuadraticOscillator_le_two_nearEndpoint
      epsilon frequency radius hepsilon hfrequency hradius
  have hpositive :=
    Complex.norm_integral_Ioi_dampedQuadraticOscillator_le_two_nearEndpoint
      epsilon frequency radius hepsilon hfrequency hradius
  have htriangle :
      ‖(∫ x in Set.Iic (-radius),
            Complex.dampedQuadraticOscillator epsilon frequency x) +
          (∫ x in Set.Ioi radius,
            Complex.dampedQuadraticOscillator epsilon frequency x)‖ ≤
        ‖∫ x in Set.Iic (-radius),
          Complex.dampedQuadraticOscillator epsilon frequency x‖ +
        ‖∫ x in Set.Ioi radius,
          Complex.dampedQuadraticOscillator epsilon frequency x‖ :=
    norm_add_le
      (∫ x in Set.Iic (-radius),
        Complex.dampedQuadraticOscillator epsilon frequency x)
      (∫ x in Set.Ioi radius,
        Complex.dampedQuadraticOscillator epsilon frequency x)
  have htails := le_trans htriangle (add_le_add hnegative hpositive)
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * radius⁻¹) +
            (((2 * ‖frequency‖)⁻¹ + (2 * ‖frequency‖)⁻¹) * radius⁻¹))
      hdecomposition.symm
      htails

/-- Exact whole-line integral of a damped quadratic oscillation centered at an
arbitrary stationary point.  Translation changes neither the value nor the
integrability hypotheses. -/
theorem Complex.integral_centeredDampedQuadratic
    (epsilon frequency center : ℝ)
    (hepsilon : 0 < epsilon) :
    (∫ x : ℝ,
      Complex.exp
        ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
          (((x - center : ℝ) : ℂ) ^ 2))) =
      (Real.pi /
        -(-(epsilon : ℂ) + Complex.I * (frequency : ℂ))) ^
          (1 / 2 : ℂ) := by
  let f : ℝ → ℂ :=
    fun y : ℝ =>
      Complex.exp
        ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) * (y : ℂ) ^ 2)
  have htranslate :
      (∫ x : ℝ, f (x - center)) = ∫ y : ℝ, f y :=
    integral_sub_right_eq_self f center
  exact
    Eq.trans
      htranslate
      (Complex.integral_dampedQuadratic epsilon frequency hepsilon)

/-- A centered damped quadratic oscillation is integrable on the real line. -/
theorem Complex.integrable_centeredDampedQuadratic
    (epsilon frequency center : ℝ)
    (hepsilon : 0 < epsilon) :
    Integrable
      (fun x : ℝ =>
        Complex.exp
          ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
            (((x - center : ℝ) : ℂ) ^ 2))) := by
  let f : ℝ → ℂ :=
    fun y : ℝ =>
      Complex.exp
        ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) * (y : ℂ) ^ 2)
  have hf : Integrable f :=
    Complex.integrable_dampedQuadratic epsilon frequency hepsilon
  exact hf.comp_sub_right center

/-- The exact damped Gaussian value has a boundary value when damping tends
to zero, provided the limiting base lies in the principal `cpow` slit plane.
The slit-plane hypothesis records the branch choice explicitly. -/
theorem Complex.tendsto_dampedQuadraticIntegralValue_nhdsWithin_zero
    (frequency : ℝ)
    (hfrequency : frequency ≠ 0)
    (hslit :
      (Real.pi /
        -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) ∈
          Complex.slitPlane) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        (Real.pi /
          -(-(epsilon : ℂ) + Complex.I * (frequency : ℂ))) ^
            (1 / 2 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝
        ((Real.pi /
          -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) ^
            (1 / 2 : ℂ))) := by
  have hfrequency_complex : (frequency : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hfrequency
  have hI_ne : Complex.I ≠ 0 :=
    Complex.I_ne_zero
  have hproduct_ne : Complex.I * (frequency : ℂ) ≠ 0 :=
    mul_ne_zero hI_ne hfrequency_complex
  have hdenominator_ne :
      -(-(0 : ℂ) + Complex.I * (frequency : ℂ)) ≠ 0 := by
    have hsum : -(0 : ℂ) + Complex.I * (frequency : ℂ) =
        Complex.I * (frequency : ℂ) :=
      Eq.trans
        (congrArg (fun value : ℂ => value + Complex.I * (frequency : ℂ))
          (neg_zero : -(0 : ℂ) = 0))
        (zero_add (Complex.I * (frequency : ℂ)))
    have hsum_ne :
        -(0 : ℂ) + Complex.I * (frequency : ℂ) ≠ 0 :=
      Eq.subst
        (motive := fun value : ℂ => value ≠ 0)
        hsum.symm
        hproduct_ne
    exact neg_ne_zero.mpr hsum_ne
  have hdenominator_continuous :
      ContinuousAt
        (fun epsilon : ℝ =>
          -(-(epsilon : ℂ) + Complex.I * (frequency : ℂ))) 0 :=
    (Complex.continuous_ofReal.neg.add continuous_const).neg.continuousAt
  have hbase_continuous :
      ContinuousAt
        (fun epsilon : ℝ =>
          (Real.pi : ℂ) /
            -(-(epsilon : ℂ) + Complex.I * (frequency : ℂ))) 0 :=
    continuousAt_const.div hdenominator_continuous hdenominator_ne
  have hbase_tendsto :
      Filter.Tendsto
        (fun epsilon : ℝ =>
          (Real.pi : ℂ) /
            -(-(epsilon : ℂ) + Complex.I * (frequency : ℂ)))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝
          ((Real.pi : ℂ) /
            -(-(0 : ℂ) + Complex.I * (frequency : ℂ)))) :=
    hbase_continuous.tendsto.mono_left inf_le_left
  exact
    hbase_tendsto.cpow tendsto_const_nhds hslit

/-- The zero-damping Gaussian base has the canonical positive-imaginary
normal form `(π * I) / frequency`. -/
theorem Complex.dampedQuadraticIntegralValue_zero_base_eq
    (frequency : ℝ) :
    (Real.pi : ℂ) /
        -(-(0 : ℂ) + Complex.I * (frequency : ℂ)) =
      ((Real.pi : ℂ) * Complex.I) / (frequency : ℂ) := by
  have hinner :
      -(0 : ℂ) + Complex.I * (frequency : ℂ) =
        Complex.I * (frequency : ℂ) :=
    Eq.trans
      (congrArg (fun value : ℂ => value + Complex.I * (frequency : ℂ))
        (neg_zero : -(0 : ℂ) = 0))
      (zero_add (Complex.I * (frequency : ℂ)))
  have hdenominator :
      -(-(0 : ℂ) + Complex.I * (frequency : ℂ)) =
        (-Complex.I) * (frequency : ℂ) :=
    Eq.trans
      (congrArg Neg.neg hinner)
      (neg_mul Complex.I (frequency : ℂ)).symm
  have hdiv_neg_I :
      (Real.pi : ℂ) / (-Complex.I) = (Real.pi : ℂ) * Complex.I := by
    exact
      Eq.trans
        (div_neg (Real.pi : ℂ))
        (Eq.trans
          (congrArg Neg.neg (Complex.div_I (Real.pi : ℂ)))
          (neg_neg ((Real.pi : ℂ) * Complex.I)))
  exact
    Eq.trans
      (congrArg (fun denominator : ℂ => (Real.pi : ℂ) / denominator)
        hdenominator)
      (Eq.trans
        (div_mul_eq_div_div (Real.pi : ℂ) (-Complex.I)
          (frequency : ℂ))
        (congrArg (fun value : ℂ => value / (frequency : ℂ)) hdiv_neg_I))

/-- Canonical positive-frequency quadratic stationary-phase boundary value. -/
def Complex.quadraticStationaryPhaseBoundaryValue
    (frequency : ℝ) : ℂ :=
  (((Real.pi : ℂ) * Complex.I) / (frequency : ℂ)) ^ (1 / 2 : ℂ)

/-- The zero-damping Gaussian closed form is the canonical stationary-phase
boundary value. -/
theorem Complex.dampedQuadraticIntegralValue_zero_eq_boundaryValue
    (frequency : ℝ) :
    ((Real.pi /
        -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) ^
          (1 / 2 : ℂ)) =
      Complex.quadraticStationaryPhaseBoundaryValue frequency := by
  exact
    congrArg
      (fun base : ℂ => base ^ (1 / 2 : ℂ))
      (Complex.dampedQuadraticIntegralValue_zero_base_eq frequency)

/-- Norm of the zero-damping stationary-phase value, expressed as the real
half-power of the normalized Gaussian base. -/
theorem Complex.norm_dampedQuadraticIntegralValue_zero
    (frequency : ℝ) :
    ‖((Real.pi /
        -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) ^
          (1 / 2 : ℂ))‖ =
      Complex.abs
          ((Real.pi : ℂ) /
            -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) ^
        (1 / 2 : ℝ) := by
  let base : ℂ :=
    (Real.pi : ℂ) /
      -(-(0 : ℂ) + Complex.I * (frequency : ℂ))
  have hnorm : ‖base ^ (1 / 2 : ℂ)‖ = Complex.abs (base ^ (1 / 2 : ℂ)) :=
    Complex.norm_eq_abs (base ^ (1 / 2 : ℂ))
  have hcomplex_half : (1 / 2 : ℂ) = (2 : ℂ)⁻¹ :=
    one_div (2 : ℂ)
  have hreal_half : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ :=
    one_div (2 : ℝ)
  have habs :
      Complex.abs (base ^ (1 / 2 : ℂ)) =
        Complex.abs base ^ (1 / 2 : ℝ) :=
    Eq.trans
      (congrArg (fun exponent : ℂ => Complex.abs (base ^ exponent))
        hcomplex_half)
      (Eq.trans
        (Complex.abs_cpow_inv_nat base 2)
        (congrArg (fun exponent : ℝ => Complex.abs base ^ exponent)
          hreal_half.symm))
  exact hnorm.trans habs

/-- Modulus of the zero-damping Gaussian base at positive frequency. -/
theorem Complex.abs_dampedQuadraticIntegralValue_zero_base
    (frequency : ℝ)
    (hfrequency : 0 < frequency) :
    Complex.abs
        ((Real.pi : ℂ) /
          -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) =
      Real.pi / frequency := by
  have hbase :=
    Complex.dampedQuadraticIntegralValue_zero_base_eq frequency
  have habs_div :
      Complex.abs
          (((Real.pi : ℂ) * Complex.I) / (frequency : ℂ)) =
        Complex.abs ((Real.pi : ℂ) * Complex.I) /
          Complex.abs (frequency : ℂ) :=
    IsAbsoluteValue.abv_div Complex.abs
      ((Real.pi : ℂ) * Complex.I) (frequency : ℂ)
  have habs_mul :
      Complex.abs ((Real.pi : ℂ) * Complex.I) =
        Complex.abs (Real.pi : ℂ) * Complex.abs Complex.I :=
    map_mul Complex.abs (Real.pi : ℂ) Complex.I
  have hpi_abs : Complex.abs (Real.pi : ℂ) = Real.pi :=
    Complex.abs_of_nonneg Real.pi_nonneg
  have hfrequency_abs :
      Complex.abs (frequency : ℂ) = frequency :=
    Complex.abs_of_nonneg (le_of_lt hfrequency)
  exact
    Eq.trans
      (congrArg Complex.abs hbase)
      (Eq.trans
        habs_div
        (Eq.trans
          (congrArg
            (fun numerator : ℝ =>
              numerator / Complex.abs (frequency : ℂ))
            habs_mul)
          (Eq.trans
            (congrArg
              (fun value : ℝ =>
                (value * Complex.abs Complex.I) /
                  Complex.abs (frequency : ℂ))
              hpi_abs)
            (Eq.trans
              (congrArg
                (fun denominator : ℝ =>
                  (Real.pi * Complex.abs Complex.I) / denominator)
                hfrequency_abs)
              (Eq.trans
                (congrArg
                  (fun value : ℝ => (Real.pi * value) / frequency)
                  Complex.abs_I)
                (congrArg (fun value : ℝ => value / frequency)
                  (mul_one Real.pi)))))))

/-- Canonical stationary-phase magnitude at positive frequency. -/
theorem Complex.norm_quadraticStationaryPhaseBoundaryValue
    (frequency : ℝ)
    (hfrequency : 0 < frequency) :
    ‖Complex.quadraticStationaryPhaseBoundaryValue frequency‖ =
      (Real.pi / frequency) ^ (1 / 2 : ℝ) := by
  have hzero_norm :=
    Complex.norm_dampedQuadraticIntegralValue_zero frequency
  have hboundary :=
    Complex.dampedQuadraticIntegralValue_zero_eq_boundaryValue frequency
  have habs :=
    Complex.abs_dampedQuadraticIntegralValue_zero_base
      frequency hfrequency
  exact
    Eq.trans
      (congrArg norm hboundary.symm)
      (Eq.trans
        hzero_norm
        (congrArg (fun value : ℝ => value ^ (1 / 2 : ℝ)) habs))

/-- For positive frequency, the zero-damping Gaussian base lies in the
principal `cpow` slit plane; its imaginary part is `π / frequency > 0`. -/
theorem Complex.dampedQuadraticIntegralValue_zero_base_mem_slitPlane
    (frequency : ℝ)
    (hfrequency : 0 < frequency) :
    (Real.pi /
      -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) ∈
        Complex.slitPlane := by
  have hbase :
      (Real.pi : ℂ) /
          -(-(0 : ℂ) + Complex.I * (frequency : ℂ)) =
        ((Real.pi : ℂ) * Complex.I) / (frequency : ℂ) := by
    exact Complex.dampedQuadraticIntegralValue_zero_base_eq frequency
  have him :
      (((Real.pi : ℂ) /
          -(-(0 : ℂ) + Complex.I * (frequency : ℂ))).im) =
        Real.pi / frequency := by
    exact
      Eq.trans
        (congrArg Complex.im hbase)
        (Eq.trans
          (Complex.div_ofReal_im ((Real.pi : ℂ) * Complex.I) frequency)
          (congrArg (fun value : ℝ => value / frequency)
            (Eq.trans
              (Complex.mul_I_im (Real.pi : ℂ))
              (Complex.ofReal_re Real.pi))))
  have him_pos :
      0 < ((Real.pi : ℂ) /
        -(-(0 : ℂ) + Complex.I * (frequency : ℂ))).im :=
    Eq.subst
      (motive := fun value : ℝ => 0 < value)
      him.symm
      (div_pos Real.pi_pos hfrequency)
  exact Or.inr (ne_of_gt him_pos)

/-- Positive-frequency specialization of the zero-damping boundary-value
theorem, with the principal branch discharged canonically. -/
theorem Complex.tendsto_dampedQuadraticIntegralValue_nhdsWithin_zero_of_pos
    (frequency : ℝ)
    (hfrequency : 0 < frequency) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        (Real.pi /
          -(-(epsilon : ℂ) + Complex.I * (frequency : ℂ))) ^
            (1 / 2 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝
        ((Real.pi /
          -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) ^
            (1 / 2 : ℂ))) := by
  exact
    Complex.tendsto_dampedQuadraticIntegralValue_nhdsWithin_zero
      frequency (ne_of_gt hfrequency)
      (Complex.dampedQuadraticIntegralValue_zero_base_mem_slitPlane
        frequency hfrequency)

/-- Exact Abel-regularized quadratic stationary-phase limit at the origin. -/
theorem Complex.tendsto_integral_dampedQuadratic_nhdsWithin_zero_of_pos
    (frequency : ℝ)
    (hfrequency : 0 < frequency) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        ∫ x : ℝ,
          Complex.exp
            ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
              (x : ℂ) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝
        ((Real.pi /
          -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) ^
            (1 / 2 : ℂ))) := by
  have hvalue :=
    Complex.tendsto_dampedQuadraticIntegralValue_nhdsWithin_zero_of_pos
      frequency hfrequency
  have hepsilon_pos :
      ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < epsilon :=
    self_mem_nhdsWithin
  have heq :
      ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (∫ x : ℝ,
          Complex.exp
            ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
              (x : ℂ) ^ 2)) =
          (Real.pi /
            -(-(epsilon : ℂ) + Complex.I * (frequency : ℂ))) ^
              (1 / 2 : ℂ) :=
    hepsilon_pos.mono
      (fun epsilon hepsilon =>
        Complex.integral_dampedQuadratic epsilon frequency hepsilon)
  exact hvalue.congr' (Filter.EventuallyEq.symm heq)

/-- Exact Abel-regularized quadratic stationary-phase limit at an arbitrary
stationary center. -/
theorem Complex.tendsto_integral_centeredDampedQuadratic_nhdsWithin_zero_of_pos
    (frequency center : ℝ)
    (hfrequency : 0 < frequency) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        ∫ x : ℝ,
          Complex.exp
            ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
              (((x - center : ℝ) : ℂ) ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝
        ((Real.pi /
          -(-(0 : ℂ) + Complex.I * (frequency : ℂ))) ^
            (1 / 2 : ℂ))) := by
  have hvalue :=
    Complex.tendsto_dampedQuadraticIntegralValue_nhdsWithin_zero_of_pos
      frequency hfrequency
  have hepsilon_pos :
      ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < epsilon :=
    self_mem_nhdsWithin
  have heq :
      ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (∫ x : ℝ,
          Complex.exp
            ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
              (((x - center : ℝ) : ℂ) ^ 2))) =
          (Real.pi /
            -(-(epsilon : ℂ) + Complex.I * (frequency : ℂ))) ^
              (1 / 2 : ℂ) :=
    hepsilon_pos.mono
      (fun epsilon hepsilon =>
        Complex.integral_centeredDampedQuadratic
          epsilon frequency center hepsilon)
  exact hvalue.congr' (Filter.EventuallyEq.symm heq)

/-- Normalized exact Abel-regularized stationary-phase theorem at an arbitrary
center. -/
theorem Complex.tendsto_integral_centeredDampedQuadratic_boundaryValue
    (frequency center : ℝ)
    (hfrequency : 0 < frequency) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        ∫ x : ℝ,
          Complex.exp
            ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
              (((x - center : ℝ) : ℂ) ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (Complex.quadraticStationaryPhaseBoundaryValue frequency)) := by
  have hraw :=
    Complex.tendsto_integral_centeredDampedQuadratic_nhdsWithin_zero_of_pos
      frequency center hfrequency
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        Filter.Tendsto
          (fun epsilon : ℝ =>
            ∫ x : ℝ,
              Complex.exp
                ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
                  (((x - center : ℝ) : ℂ) ^ 2)))
          (nhdsWithin 0 (Set.Ioi 0))
          (𝓝 value))
      (Complex.dampedQuadraticIntegralValue_zero_eq_boundaryValue frequency)
      hraw

/-- Pointwise removal of the Gaussian damping, stated before normalization of
the value at `epsilon = 0`. -/
theorem Complex.tendsto_exp_dampedQuadratic_nhdsWithin_zero
    (frequency x : ℝ) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        Complex.exp
          ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
            (x : ℂ) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝
        (Complex.exp
          ((-(0 : ℂ) + Complex.I * (frequency : ℂ)) *
            (x : ℂ) ^ 2))) := by
  have hcoefficient :
      Continuous
        (fun epsilon : ℝ =>
          -(epsilon : ℂ) + Complex.I * (frequency : ℂ)) :=
    Complex.continuous_ofReal.neg.add continuous_const
  have hexponent :
      Continuous
        (fun epsilon : ℝ =>
          (-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
            (x : ℂ) ^ 2) :=
    hcoefficient.mul continuous_const
  have hintegrand :
      Continuous
        (fun epsilon : ℝ =>
          Complex.exp
            ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
              (x : ℂ) ^ 2)) :=
    Complex.continuous_exp.comp hexponent
  exact
    (hintegrand.tendsto 0).mono_left inf_le_left

/-- On every finite interval, removing the positive Gaussian damping commutes
with integration.  This is the local dominated-convergence step used before
the whole-line tail estimate. -/
theorem Complex.tendsto_intervalIntegral_exp_dampedQuadratic
    (frequency left right : ℝ) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        ∫ x in left..right,
          Complex.exp
            ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
              (x : ℂ) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝
        (∫ x in left..right,
          Complex.exp
            ((-(0 : ℂ) + Complex.I * (frequency : ℂ)) *
              (x : ℂ) ^ 2))) := by
  let F : ℝ → ℝ → ℂ :=
    fun epsilon x =>
      Complex.exp
        ((-(epsilon : ℂ) + Complex.I * (frequency : ℂ)) *
          (x : ℂ) ^ 2)
  let f : ℝ → ℂ :=
    fun x =>
      Complex.exp
        ((-(0 : ℂ) + Complex.I * (frequency : ℂ)) *
          (x : ℂ) ^ 2)
  have hepsilon_pos :
      ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < epsilon :=
    self_mem_nhdsWithin
  have hmeasurable :
      ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0),
        AEStronglyMeasurable
          (F epsilon)
          (MeasureTheory.volume.restrict (Set.uIoc left right)) := by
    exact Filter.Eventually.of_forall
      (fun epsilon =>
        (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.pow 2))).aestronglyMeasurable)
  have hbound :
      ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ x : ℝ ∂MeasureTheory.volume,
          x ∈ Set.uIoc left right → ‖F epsilon x‖ ≤ (1 : ℝ) := by
    exact hepsilon_pos.mono
      (fun epsilon hepsilon =>
        Filter.Eventually.of_forall
          (fun x _hx =>
            have hexponent_nonpos : -epsilon * x ^ 2 ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg
                (neg_nonpos.mpr (le_of_lt hepsilon))
                (sq_nonneg x)
            have hexp_le : Real.exp (-epsilon * x ^ 2) ≤ 1 :=
              Real.exp_le_one_iff.mpr hexponent_nonpos
            Eq.subst
              (motive := fun r : ℝ => r ≤ 1)
              (Complex.norm_exp_dampedQuadratic epsilon frequency x).symm
              hexp_le))
  have hbound_integrable :
      IntervalIntegrable
        (fun _x : ℝ => (1 : ℝ))
        MeasureTheory.volume left right :=
    intervalIntegrable_const
  have hpointwise :
      ∀ᵐ x : ℝ ∂MeasureTheory.volume,
        x ∈ Set.uIoc left right →
          Filter.Tendsto
            (fun epsilon : ℝ => F epsilon x)
            (nhdsWithin 0 (Set.Ioi 0))
            (𝓝 (f x)) := by
    exact Filter.Eventually.of_forall
      (fun x _hx =>
        Complex.tendsto_exp_dampedQuadratic_nhdsWithin_zero frequency x)
  exact
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _x : ℝ => (1 : ℝ))
      hmeasurable hbound hbound_integrable hpointwise

/-- Removing zero damping recovers the pure quadratic oscillator exactly. -/
theorem Complex.dampedQuadraticOscillator_zero_eq_quadraticOscillation
    (frequency x : ℝ) :
    Complex.dampedQuadraticOscillator 0 frequency x =
      Complex.quadraticOscillation frequency x := by
  have hcoefficient :
      Complex.dampedQuadraticCoefficient 0 frequency =
        Complex.I * (frequency : ℂ) := by
    exact
      (congrArg
        (fun value : ℂ => value + Complex.I * (frequency : ℂ))
        (neg_zero : -(0 : ℂ) = 0)).trans
        (zero_add (Complex.I * (frequency : ℂ)))
  exact
    congrArg Complex.exp
      (congrArg
        (fun coefficient : ℂ => coefficient * (x : ℂ) ^ 2)
        hcoefficient)

/-- At every fixed symmetric radius, the Abel boundary value differs from the
undamped truncation by at most the uniform two-tail budget. -/
theorem Complex.norm_quadraticStationaryPhaseBoundaryValue_sub_symmetricTruncation_le
    (frequency : ℝ)
    (hfrequency : 0 < frequency)
    (n : ℕ) :
    ‖Complex.quadraticStationaryPhaseBoundaryValue frequency -
        Complex.quadraticOscillationSymmetricTruncation frequency n‖ ≤
      Complex.quadraticOscillationSymmetricTailBudget frequency n := by
  let radius : ℝ := ((n + 1 : ℕ) : ℝ)
  have hradius : 0 < radius :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ n)
  have hfull_raw :=
    Complex.tendsto_integral_dampedQuadratic_nhdsWithin_zero_of_pos
      frequency hfrequency
  have hfull :
      Filter.Tendsto
        (fun epsilon : ℝ =>
          ∫ x : ℝ,
            Complex.dampedQuadraticOscillator epsilon frequency x)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (Complex.quadraticStationaryPhaseBoundaryValue frequency)) := by
    exact
      Eq.subst
        (motive := fun value : ℂ =>
          Filter.Tendsto
            (fun epsilon : ℝ =>
              ∫ x : ℝ,
                Complex.dampedQuadraticOscillator epsilon frequency x)
            (nhdsWithin 0 (Set.Ioi 0))
            (𝓝 value))
        (Complex.dampedQuadraticIntegralValue_zero_eq_boundaryValue frequency)
        hfull_raw
  have hfinite_raw :=
    Complex.tendsto_intervalIntegral_exp_dampedQuadratic
      frequency (-radius) radius
  have hzero_integral :
      (∫ x in -radius..radius,
          Complex.dampedQuadraticOscillator 0 frequency x) =
        ∫ x in -radius..radius,
          Complex.quadraticOscillation frequency x :=
    intervalIntegral.integral_congr
      (fun x _hx =>
        Complex.dampedQuadraticOscillator_zero_eq_quadraticOscillation
          frequency x)
  have hfinite :
      Filter.Tendsto
        (fun epsilon : ℝ =>
          ∫ x in -radius..radius,
            Complex.dampedQuadraticOscillator epsilon frequency x)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (Complex.quadraticOscillationSymmetricTruncation frequency n)) := by
    exact
      Eq.subst
        (motive := fun value : ℂ =>
          Filter.Tendsto
            (fun epsilon : ℝ =>
              ∫ x in -radius..radius,
                Complex.dampedQuadraticOscillator epsilon frequency x)
            (nhdsWithin 0 (Set.Ioi 0))
            (𝓝 value))
        hzero_integral
        hfinite_raw
  have hdifference :
      Filter.Tendsto
        (fun epsilon : ℝ =>
          (∫ x : ℝ,
              Complex.dampedQuadraticOscillator epsilon frequency x) -
            (∫ x in -radius..radius,
              Complex.dampedQuadraticOscillator epsilon frequency x))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝
          (Complex.quadraticStationaryPhaseBoundaryValue frequency -
            Complex.quadraticOscillationSymmetricTruncation frequency n)) :=
    hfull.sub hfinite
  have hnorm_limit := tendsto_norm.comp hdifference
  have hepsilon_pos :
      ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < epsilon :=
    self_mem_nhdsWithin
  have heventually :
      ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ‖(∫ x : ℝ,
              Complex.dampedQuadraticOscillator epsilon frequency x) -
            (∫ x in -radius..radius,
              Complex.dampedQuadraticOscillator epsilon frequency x)‖ ≤
          Complex.quadraticOscillationSymmetricTailBudget frequency n :=
    hepsilon_pos.mono
      (fun epsilon hepsilon =>
        Complex.norm_integral_dampedQuadraticOscillator_sub_symmetricInterval_le
          epsilon frequency radius hepsilon (ne_of_gt hfrequency) hradius)
  exact le_of_tendsto hnorm_limit heventually

/-- The undamped symmetric quadratic truncations converge to the Abel
stationary-phase boundary value. -/
theorem Complex.tendsto_quadraticOscillationSymmetricTruncation_boundaryValue
    (frequency : ℝ)
    (hfrequency : 0 < frequency) :
    Filter.Tendsto
      (Complex.quadraticOscillationSymmetricTruncation frequency)
      Filter.atTop
      (𝓝 (Complex.quadraticStationaryPhaseBoundaryValue frequency)) := by
  exact tendsto_iff_dist_tendsto_zero.mpr (by
    have hdistance_nonneg :
      ∀ᶠ n : ℕ in Filter.atTop,
        0 ≤
          dist
            (Complex.quadraticOscillationSymmetricTruncation frequency n)
            (Complex.quadraticStationaryPhaseBoundaryValue frequency) :=
      Filter.Eventually.of_forall
        (fun n => dist_nonneg)
    have hdistance_bound :
      ∀ᶠ n : ℕ in Filter.atTop,
        dist
            (Complex.quadraticOscillationSymmetricTruncation frequency n)
            (Complex.quadraticStationaryPhaseBoundaryValue frequency) ≤
          Complex.quadraticOscillationSymmetricTailBudget frequency n :=
      Filter.Eventually.of_forall
        (fun n => by
          have hbound :=
            Complex.norm_quadraticStationaryPhaseBoundaryValue_sub_symmetricTruncation_le
              frequency hfrequency n
          have hdistance :
              dist
                  (Complex.quadraticOscillationSymmetricTruncation frequency n)
                  (Complex.quadraticStationaryPhaseBoundaryValue frequency) =
                ‖Complex.quadraticStationaryPhaseBoundaryValue frequency -
                  Complex.quadraticOscillationSymmetricTruncation frequency n‖ := by
            exact
              (dist_eq_norm
                (Complex.quadraticOscillationSymmetricTruncation frequency n)
                (Complex.quadraticStationaryPhaseBoundaryValue frequency)).trans
                (norm_sub_rev
                  (Complex.quadraticOscillationSymmetricTruncation frequency n)
                  (Complex.quadraticStationaryPhaseBoundaryValue frequency))
          exact
            Eq.subst
              (motive := fun value : ℝ =>
                value ≤
                  Complex.quadraticOscillationSymmetricTailBudget frequency n)
              hdistance.symm
              hbound)
    exact
      squeeze_zero' hdistance_nonneg hdistance_bound
        (Complex.tendsto_quadraticOscillationSymmetricTailBudget_zero frequency))

/-- Exact quadratic stationary-phase improper integral for positive
frequency. -/
theorem Complex.quadraticOscillatoryImproperIntegral_eq_boundaryValue
    (frequency : ℝ)
    (hfrequency : 0 < frequency) :
    Complex.quadraticOscillatoryImproperIntegral frequency =
      Complex.quadraticStationaryPhaseBoundaryValue frequency := by
  have himproper :=
    Complex.tendsto_quadraticOscillationSymmetricTruncation_improperIntegral
      frequency (ne_of_gt hfrequency)
  have hboundary :=
    Complex.tendsto_quadraticOscillationSymmetricTruncation_boundaryValue
      frequency hfrequency
  exact tendsto_nhds_unique himproper hboundary

/-- Exact norm of the genuine improper quadratic stationary-phase integral. -/
theorem Complex.norm_quadraticOscillatoryImproperIntegral
    (frequency : ℝ)
    (hfrequency : 0 < frequency) :
    ‖Complex.quadraticOscillatoryImproperIntegral frequency‖ =
      (Real.pi / frequency) ^ (1 / 2 : ℝ) := by
  have hequality :=
    Complex.quadraticOscillatoryImproperIntegral_eq_boundaryValue
      frequency hfrequency
  exact
    (congrArg norm hequality).trans
      (Complex.norm_quadraticStationaryPhaseBoundaryValue
        frequency hfrequency)

end

end LFunctions
end Boundary
