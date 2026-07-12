import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedDerivativeChain

/-!
# Interval regularity for phase-adapted logarithmic packets

A uniform positive derivative gap on the quantitative support makes every
reciprocal coefficient regular there.  The transformed amplitudes and the
oscillator derivative are consequently interval integrable, with no regularity
hypotheses exported to downstream packet estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

theorem Complex.logarithmicPhaseQuantitativeSupport_mem_positive
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    {x : ℝ}
    (hx : x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
      Complex.logarithmicPhaseQuantitativeSupportRight b]]) :
    0 < x := by
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hxIcc : x ∈ Set.Icc
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) :=
    (Set.uIcc_of_le hleftRight).mp hx
  have hleftPos :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  exact lt_of_lt_of_le hleftPos hxIcc.1

theorem Complex.continuousOn_logarithmicPhaseAdaptedCoefficient
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousOn
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
      [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]] := by
  intro x hx
  have hxPos :=
    Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
  have hat :=
    Complex.continuousAt_logarithmicPhaseAdaptedCoefficient_of_gap
      t m hxPos hgap (hlower x hx)
  exact hat.continuousWithinAt

theorem Complex.continuousOn_logarithmicPhaseAdaptedCoefficientDerivative
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousOn
      (Complex.realPhaseIntegrationCoefficientDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
      [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]] := by
  intro x hx
  have hxPos :=
    Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
  have hat :=
    Complex.continuousAt_logarithmicPhaseAdaptedCoefficientDerivative_of_gap
      t m hxPos hgap (hlower x hx)
  exact hat.continuousWithinAt

theorem Complex.continuousOn_logarithmicPhaseAdaptedFirstTransform
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousOn
      (Complex.nonstationaryFirstTransformedAmplitude
        (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
        (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
        (Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
        (Complex.realPhaseIntegrationCoefficientDerivative
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
          (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)))
      [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]] := by
  intro x hx
  have hxPos :=
    Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
  have hat :=
    Complex.continuousAt_logarithmicPhaseAdaptedFirstTransform_of_gap
      t a b m hxPos hgap (hlower x hx)
  exact hat.continuousWithinAt

theorem Complex.continuousOn_logarithmicPhaseAdaptedSecondTransform
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousOn
      (Complex.nonstationarySecondTransformedAmplitude
        (Complex.nonstationaryFirstTransformedDerivativeExplicit
          (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
          (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
          (Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b)
          (Complex.realPhaseIntegrationCoefficient
            (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
          (Complex.realPhaseIntegrationCoefficientDerivative
            (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
            (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
          (Complex.realPhaseIntegrationCoefficientSecondDerivative
            (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
            (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)
            (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t)))
        (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
        (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
        (Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
        (Complex.realPhaseIntegrationCoefficientDerivative
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
          (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)))
      [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]] := by
  intro x hx
  have hxPos :=
    Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
  have hat :=
    Complex.continuousAt_logarithmicPhaseAdaptedSecondTransform_of_gap
      t a b m hxPos hgap (hlower x hx)
  exact hat.continuousWithinAt

theorem Complex.intervalIntegrable_logarithmicPhaseAdaptedFirstTransform
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    IntervalIntegrable
      (Complex.nonstationaryFirstTransformedAmplitude
        (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
        (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
        (Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
        (Complex.realPhaseIntegrationCoefficientDerivative
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
          (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)))
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  have hcontinuous :=
    Complex.continuousOn_logarithmicPhaseAdaptedFirstTransform
      t a b m gap ha hab hgap hlower
  exact hcontinuous.intervalIntegrable

theorem Complex.intervalIntegrable_logarithmicPhaseAdaptedSecondTransform
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    IntervalIntegrable
      (Complex.nonstationarySecondTransformedAmplitude
        (Complex.nonstationaryFirstTransformedDerivativeExplicit
          (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
          (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
          (Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b)
          (Complex.realPhaseIntegrationCoefficient
            (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
          (Complex.realPhaseIntegrationCoefficientDerivative
            (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
            (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
          (Complex.realPhaseIntegrationCoefficientSecondDerivative
            (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
            (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)
            (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t)))
        (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
        (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
        (Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
        (Complex.realPhaseIntegrationCoefficientDerivative
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
          (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)))
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  have hcontinuous :=
    Complex.continuousOn_logarithmicPhaseAdaptedSecondTransform
      t a b m gap ha hab hgap hlower
  exact hcontinuous.intervalIntegrable

theorem Complex.continuousOn_logarithmicPhaseAdaptedOscillatorDerivative
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ContinuousOn
      (Complex.logarithmicPhaseAdaptedOscillatorDerivative t m)
      [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]] := by
  intro x hx
  have hxPos :=
    Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
  exact (Complex.hasDerivAt_logarithmicPhaseAdaptedOscillator
    t m hxPos).continuousAt.continuousWithinAt

theorem Complex.intervalIntegrable_logarithmicPhaseAdaptedOscillatorDerivative
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (Complex.logarithmicPhaseAdaptedOscillatorDerivative t m)
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  exact (Complex.continuousOn_logarithmicPhaseAdaptedOscillatorDerivative
    t a b m ha hab).intervalIntegrable

end
end LFunctions
end Boundary
