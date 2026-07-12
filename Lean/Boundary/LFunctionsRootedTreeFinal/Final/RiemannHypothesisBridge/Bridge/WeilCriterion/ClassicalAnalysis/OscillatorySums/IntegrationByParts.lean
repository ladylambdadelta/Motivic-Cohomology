import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!
# Generic complex oscillatory integration by parts

This base owner is independent of every phase model.  Both the real-phase
nonstationary library and the Gaussian-damped stationary library consume it.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

/-- Generic complex-valued one-step integration by parts.  The cancellation
identity `coefficient * oscillatorDerivative = oscillator` is explicit. -/
theorem Complex.intervalIntegral_oscillator_eq_boundary_sub_remainder
    (oscillator coefficient : ℝ → ℂ)
    (oscillatorDerivative coefficientDerivative : ℝ → ℂ)
    (left right : ℝ)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt coefficient (coefficientDerivative x) x)
    (hoscillator :
      ∀ x ∈ [[left, right]],
        HasDerivAt oscillator (oscillatorDerivative x) x)
    (hcoefficientDerivative_integrable :
      IntervalIntegrable coefficientDerivative volume left right)
    (hoscillatorDerivative_integrable :
      IntervalIntegrable oscillatorDerivative volume left right)
    (hcancellation :
      ∀ x ∈ [[left, right]],
        coefficient x * oscillatorDerivative x = oscillator x) :
    (∫ x in left..right, oscillator x) =
      coefficient right * oscillator right -
        coefficient left * oscillator left -
        ∫ x in left..right,
          coefficientDerivative x * oscillator x := by
  have hintegration_by_parts :
      (∫ x in left..right,
          coefficient x * oscillatorDerivative x) =
        coefficient right * oscillator right -
          coefficient left * oscillator left -
          ∫ x in left..right,
            coefficientDerivative x * oscillator x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hcoefficient hoscillator
      hcoefficientDerivative_integrable
      hoscillatorDerivative_integrable
  have hintegral :
      (∫ x in left..right,
          coefficient x * oscillatorDerivative x) =
        ∫ x in left..right, oscillator x :=
    intervalIntegral.integral_congr hcancellation
  exact hintegral.symm.trans hintegration_by_parts

end

end LFunctions
end Boundary
