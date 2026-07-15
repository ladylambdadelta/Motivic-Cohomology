import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.NonstationaryPhase

/-!
# Amplitude-bearing nonstationary integration by parts

The generic real-phase owner treats unit-modulus oscillations.  Fourier tails
need the same identity with a differentiable complex amplitude attached.  This
file owns that product rule once, so a quantitative cutoff specialization can
iterate it without recreating the algebra of the reciprocal phase coefficient.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.realPhaseAmplitudeCoefficient
    (amplitude : ℝ → ℂ)
    (phaseDerivative : ℝ → ℝ)
    (x : ℝ) : ℂ :=
  amplitude x * Complex.realPhaseIntegrationCoefficient phaseDerivative x

def Complex.realPhaseAmplitudeCoefficientDerivative
    (amplitude amplitudeDerivative : ℝ → ℂ)
    (phaseDerivativeCoefficientDerivative : ℝ → ℂ)
    (phaseDerivative : ℝ → ℝ)
    (x : ℝ) : ℂ :=
  amplitudeDerivative x *
      Complex.realPhaseIntegrationCoefficient phaseDerivative x +
    amplitude x * phaseDerivativeCoefficientDerivative x

theorem Complex.hasDerivAt_realPhaseAmplitudeCoefficient
    (amplitude amplitudeDerivative : ℝ → ℂ)
    (phaseDerivative : ℝ → ℝ)
    (phaseDerivativeCoefficientDerivative : ℝ → ℂ)
    (x : ℝ)
    (hamplitude : HasDerivAt amplitude (amplitudeDerivative x) x)
    (hcoefficient :
      HasDerivAt
        (Complex.realPhaseIntegrationCoefficient phaseDerivative)
        (phaseDerivativeCoefficientDerivative x)
        x) :
    HasDerivAt
      (Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative)
      (Complex.realPhaseAmplitudeCoefficientDerivative
        amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
        phaseDerivative x)
      x := by
  have hproduct := hamplitude.mul hcoefficient
  exact hproduct

theorem Complex.realPhaseAmplitudeCoefficient_mul_oscillationDerivative
    (amplitude : ℝ → ℂ)
    (phase phaseDerivative : ℝ → ℝ)
    (x : ℝ)
    (hdenominator :
      Complex.realPhaseDerivativeDenominator phaseDerivative x ≠ 0) :
    Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative x *
        (Complex.realPhaseOscillation phase x *
          Complex.realPhaseDerivativeDenominator phaseDerivative x) =
      amplitude x * Complex.realPhaseOscillation phase x := by
  have hcancellation :=
    Complex.realPhaseIntegrationCoefficient_mul_deriv
      phase phaseDerivative x hdenominator
  calc
    Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative x *
        (Complex.realPhaseOscillation phase x *
          Complex.realPhaseDerivativeDenominator phaseDerivative x) =
        amplitude x *
          (Complex.realPhaseIntegrationCoefficient phaseDerivative x *
            (Complex.realPhaseOscillation phase x *
              Complex.realPhaseDerivativeDenominator phaseDerivative x)) := by
      unfold Complex.realPhaseAmplitudeCoefficient
      exact (mul_assoc
        (amplitude x)
        (Complex.realPhaseIntegrationCoefficient phaseDerivative x)
        (Complex.realPhaseOscillation phase x *
          Complex.realPhaseDerivativeDenominator phaseDerivative x))
    _ = amplitude x * Complex.realPhaseOscillation phase x :=
      congrArg (fun value : ℂ => amplitude x * value) hcancellation

theorem Complex.intervalIntegral_realPhaseAmplitudeOscillation_eq_boundary_sub_remainder
    (amplitude amplitudeDerivative : ℝ → ℂ)
    (phase phaseDerivative : ℝ → ℝ)
    (phaseDerivativeCoefficientDerivative oscillationDerivative : ℝ → ℂ)
    (left right : ℝ)
    (hamplitude :
      ∀ x ∈ [[left, right]],
        HasDerivAt amplitude (amplitudeDerivative x) x)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient phaseDerivative)
          (phaseDerivativeCoefficientDerivative x)
          x)
    (hoscillation :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation phase)
          (oscillationDerivative x)
          x)
    (hamplitudeCoefficientDerivative_integrable :
      IntervalIntegrable
        (Complex.realPhaseAmplitudeCoefficientDerivative
          amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
          phaseDerivative)
        volume left right)
    (hoscillationDerivative_integrable :
      IntervalIntegrable oscillationDerivative volume left right)
    (hoscillationDerivative_eq :
      ∀ x ∈ [[left, right]],
        oscillationDerivative x =
          Complex.realPhaseOscillation phase x *
            Complex.realPhaseDerivativeDenominator phaseDerivative x)
    (hdenominator :
      ∀ x ∈ [[left, right]],
        Complex.realPhaseDerivativeDenominator phaseDerivative x ≠ 0) :
    (∫ x in left..right,
        amplitude x * Complex.realPhaseOscillation phase x) =
      Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right *
          Complex.realPhaseOscillation phase right -
        Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left *
          Complex.realPhaseOscillation phase left -
        ∫ x in left..right,
          Complex.realPhaseAmplitudeCoefficientDerivative
            amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
            phaseDerivative x *
              Complex.realPhaseOscillation phase x := by
  have hamplitudeCoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative)
          (Complex.realPhaseAmplitudeCoefficientDerivative
            amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
            phaseDerivative x)
          x := by
    intro x hx
    exact
      Complex.hasDerivAt_realPhaseAmplitudeCoefficient
        amplitude amplitudeDerivative phaseDerivative
        phaseDerivativeCoefficientDerivative x
        (hamplitude x hx) (hcoefficient x hx)
  have hintegrationByParts :=
    Complex.intervalIntegral_target_eq_boundary_sub_remainder
      (fun x => amplitude x * Complex.realPhaseOscillation phase x)
      (Complex.realPhaseOscillation phase)
      (Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative)
      oscillationDerivative
      (Complex.realPhaseAmplitudeCoefficientDerivative
        amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
        phaseDerivative)
      left right
      hamplitudeCoefficient hoscillation
      hamplitudeCoefficientDerivative_integrable
      hoscillationDerivative_integrable
      (fun x hx =>
        calc
          Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative x *
              oscillationDerivative x =
            Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative x *
              (Complex.realPhaseOscillation phase x *
                Complex.realPhaseDerivativeDenominator phaseDerivative x) :=
              congrArg
                (fun value : ℂ =>
                  Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative x * value)
                (hoscillationDerivative_eq x hx)
          _ = amplitude x * Complex.realPhaseOscillation phase x :=
            Complex.realPhaseAmplitudeCoefficient_mul_oscillationDerivative
              amplitude phase phaseDerivative x (hdenominator x hx))
  exact hintegrationByParts

theorem Complex.norm_intervalIntegral_realPhaseAmplitudeOscillation_le_boundary_add_remainder
    (amplitude amplitudeDerivative : ℝ → ℂ)
    (phase phaseDerivative : ℝ → ℝ)
    (phaseDerivativeCoefficientDerivative oscillationDerivative : ℝ → ℂ)
    (left right : ℝ)
    (hleft_right : left ≤ right)
    (hamplitude :
      ∀ x ∈ [[left, right]],
        HasDerivAt amplitude (amplitudeDerivative x) x)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient phaseDerivative)
          (phaseDerivativeCoefficientDerivative x)
          x)
    (hoscillation :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation phase)
          (oscillationDerivative x)
          x)
    (hamplitudeCoefficientDerivative_integrable :
      IntervalIntegrable
        (Complex.realPhaseAmplitudeCoefficientDerivative
          amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
          phaseDerivative)
        volume left right)
    (hoscillationDerivative_integrable :
      IntervalIntegrable oscillationDerivative volume left right)
    (hoscillationDerivative_eq :
      ∀ x ∈ [[left, right]],
        oscillationDerivative x =
          Complex.realPhaseOscillation phase x *
            Complex.realPhaseDerivativeDenominator phaseDerivative x)
    (hdenominator :
      ∀ x ∈ [[left, right]],
        Complex.realPhaseDerivativeDenominator phaseDerivative x ≠ 0) :
    ‖∫ x in left..right,
        amplitude x * Complex.realPhaseOscillation phase x‖ ≤
      ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right‖ +
        ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left‖ +
        ∫ x in left..right,
          ‖Complex.realPhaseAmplitudeCoefficientDerivative
            amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
            phaseDerivative x‖ := by
  have hidentity :=
    Complex.intervalIntegral_realPhaseAmplitudeOscillation_eq_boundary_sub_remainder
      amplitude amplitudeDerivative phase phaseDerivative
      phaseDerivativeCoefficientDerivative oscillationDerivative left right
      hamplitude hcoefficient hoscillation
      hamplitudeCoefficientDerivative_integrable
      hoscillationDerivative_integrable hoscillationDerivative_eq hdenominator
  let rightBoundary : ℂ :=
    Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right *
      Complex.realPhaseOscillation phase right
  let leftBoundary : ℂ :=
    Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left *
      Complex.realPhaseOscillation phase left
  let remainder : ℂ :=
    ∫ x in left..right,
      Complex.realPhaseAmplitudeCoefficientDerivative
        amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
        phaseDerivative x * Complex.realPhaseOscillation phase x
  have htriangle :
      ‖rightBoundary - leftBoundary - remainder‖ ≤
        ‖rightBoundary‖ + ‖leftBoundary‖ + ‖remainder‖ := by
    have hfirst := norm_sub_le (rightBoundary - leftBoundary) remainder
    have hsecond := norm_sub_le rightBoundary leftBoundary
    have hsum := add_le_add_right hsecond ‖remainder‖
    exact le_trans hfirst hsum
  have hrightNorm :
      ‖rightBoundary‖ =
        ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right‖ := by
    unfold rightBoundary
    exact
      (norm_mul
        (Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right)
        (Complex.realPhaseOscillation phase right)).trans
        ((congrArg
          (fun value : ℝ =>
            ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right‖ * value)
          (Complex.norm_realPhaseOscillation phase right)).trans
          (mul_one ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right‖))
  have hleftNorm :
      ‖leftBoundary‖ =
        ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left‖ := by
    unfold leftBoundary
    exact
      (norm_mul
        (Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left)
        (Complex.realPhaseOscillation phase left)).trans
        ((congrArg
          (fun value : ℝ =>
            ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left‖ * value)
          (Complex.norm_realPhaseOscillation phase left)).trans
          (mul_one ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left‖))
  have hremainderNorm :
      ‖remainder‖ ≤
        ∫ x in left..right,
          ‖Complex.realPhaseAmplitudeCoefficientDerivative
            amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
            phaseDerivative x‖ := by
    have hnorm :=
      intervalIntegral.norm_integral_le_integral_norm (μ := volume) hleft_right
        (f := fun x : ℝ =>
          Complex.realPhaseAmplitudeCoefficientDerivative
            amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
            phaseDerivative x * Complex.realPhaseOscillation phase x)
    have hintegrand :
        Set.EqOn
          (fun x : ℝ =>
            ‖Complex.realPhaseAmplitudeCoefficientDerivative
              amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
              phaseDerivative x * Complex.realPhaseOscillation phase x‖)
          (fun x : ℝ =>
            ‖Complex.realPhaseAmplitudeCoefficientDerivative
              amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
              phaseDerivative x‖)
          [[left, right]] := by
      intro x hx
      exact
        (norm_mul
          (Complex.realPhaseAmplitudeCoefficientDerivative
            amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
            phaseDerivative x)
          (Complex.realPhaseOscillation phase x)).trans
          ((congrArg
            (fun value : ℝ =>
              ‖Complex.realPhaseAmplitudeCoefficientDerivative
                amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
                phaseDerivative x‖ * value)
            (Complex.norm_realPhaseOscillation phase x)).trans
            (mul_one
              ‖Complex.realPhaseAmplitudeCoefficientDerivative
                amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
                phaseDerivative x‖))
    have hintegral := intervalIntegral.integral_congr (μ := volume) hintegrand
    exact hnorm.trans (le_of_eq hintegral)
  have hcombined :
      ‖rightBoundary - leftBoundary - remainder‖ ≤
        ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right‖ +
          ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left‖ +
          ∫ x in left..right,
            ‖Complex.realPhaseAmplitudeCoefficientDerivative
              amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
              phaseDerivative x‖ := by
    have hboundary :
        ‖rightBoundary‖ + ‖leftBoundary‖ =
          ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right‖ +
            ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left‖ :=
      congrArg₂ (fun first second : ℝ => first + second) hrightNorm hleftNorm
    have hsum := add_le_add (le_of_eq hboundary) hremainderNorm
    exact le_trans htriangle hsum
  have hrewritten :
      (∫ x in left..right,
        amplitude x * Complex.realPhaseOscillation phase x) =
        rightBoundary - leftBoundary - remainder := by
    exact hidentity
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤
          ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative right‖ +
            ‖Complex.realPhaseAmplitudeCoefficient amplitude phaseDerivative left‖ +
            ∫ x in left..right,
              ‖Complex.realPhaseAmplitudeCoefficientDerivative
                amplitude amplitudeDerivative phaseDerivativeCoefficientDerivative
                phaseDerivative x‖)
      hrewritten.symm
      hcombined

end
end LFunctions
end Boundary
