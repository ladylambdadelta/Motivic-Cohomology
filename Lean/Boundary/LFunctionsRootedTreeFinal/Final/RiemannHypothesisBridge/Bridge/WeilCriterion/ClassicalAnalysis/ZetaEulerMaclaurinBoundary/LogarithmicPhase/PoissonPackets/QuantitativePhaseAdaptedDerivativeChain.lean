import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEndpoints

/-!
# Differential chain for phase-adapted packet integration

On an interval carrying a positive phase-derivative gap, the reciprocal phase
coefficient is twice differentiable.  Combining it with the cutoff gives the
exact first transformed derivative consumed by the second integration by
parts.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseAdaptedDerivativeDenominator_ne_zero_of_gap
    (t : ℝ) (m : ℤ) (x gap : ℝ)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    Complex.realPhaseDerivativeDenominator
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x ≠ 0 := by
  have hphase :=
    Complex.logarithmicPhaseAdaptedDerivative_ne_zero_of_gap
      t m x gap hgap hlower
  exact Complex.logarithmicPhaseAdaptedDerivativeDenominator_ne_zero
    t m x hphase

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedCoefficient_of_gap
    (t : ℝ) (m : ℤ) {x gap : ℝ}
    (hx : 0 < x)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    HasDerivAt
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
      (Complex.realPhaseIntegrationCoefficientDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t) x) x := by
  have hphaseDerivative :=
    Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhaseDerivative t m hx
  have hdenominator :=
    Complex.logarithmicPhaseAdaptedDerivativeDenominator_ne_zero_of_gap
      t m x gap hgap hlower
  exact Complex.hasDerivAt_realPhaseIntegrationCoefficient_named
    hphaseDerivative hdenominator

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedCoefficientDerivative_of_gap
    (t : ℝ) (m : ℤ) {x gap : ℝ}
    (hx : 0 < x)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    HasDerivAt
      (Complex.realPhaseIntegrationCoefficientDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
      (Complex.realPhaseIntegrationCoefficientSecondDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t) x) x := by
  have hphaseDerivative :=
    Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhaseDerivative t m hx
  have hphaseSecond :=
    Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t hx
  have hdenominator :=
    Complex.logarithmicPhaseAdaptedDerivativeDenominator_ne_zero_of_gap
      t m x gap hgap hlower
  exact Complex.hasDerivAt_realPhaseIntegrationCoefficientDerivative
    hphaseDerivative hphaseSecond hdenominator

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedFirstTransform_of_gap
    (t : ℝ) (a b m : ℤ) {x gap : ℝ}
    (hx : 0 < x)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    HasDerivAt
      (Complex.nonstationaryFirstTransformedAmplitude
        (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
        (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
        (Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
        (Complex.realPhaseIntegrationCoefficientDerivative
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
          (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)))
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
          (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t)) x) x := by
  have hamplitude :=
    Complex.hasDerivAt_logarithmicPhaseAdaptedCutoffAmplitude a b x
  have hamplitudeDerivative :=
    Complex.hasDerivAt_logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b x
  have hcoefficient :=
    Complex.hasDerivAt_logarithmicPhaseAdaptedCoefficient_of_gap
      t m hx hgap hlower
  have hcoefficientDerivative :=
    Complex.hasDerivAt_logarithmicPhaseAdaptedCoefficientDerivative_of_gap
      t m hx hgap hlower
  exact Complex.hasDerivAt_nonstationaryFirstTransformedAmplitude_explicit
    hamplitude hamplitudeDerivative hcoefficient hcoefficientDerivative

theorem Complex.continuousAt_logarithmicPhaseAdaptedCoefficient_of_gap
    (t : ℝ) (m : ℤ) {x gap : ℝ}
    (hx : 0 < x)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousAt
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)) x := by
  exact (Complex.hasDerivAt_logarithmicPhaseAdaptedCoefficient_of_gap
    t m hx hgap hlower).continuousAt

theorem Complex.continuousAt_logarithmicPhaseAdaptedCoefficientDerivative_of_gap
    (t : ℝ) (m : ℤ) {x gap : ℝ}
    (hx : 0 < x)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousAt
      (Complex.realPhaseIntegrationCoefficientDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)) x := by
  exact (Complex.hasDerivAt_logarithmicPhaseAdaptedCoefficientDerivative_of_gap
    t m hx hgap hlower).continuousAt

theorem Complex.continuousAt_logarithmicPhaseAdaptedFirstTransform_of_gap
    (t : ℝ) (a b m : ℤ) {x gap : ℝ}
    (hx : 0 < x)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousAt
      (Complex.nonstationaryFirstTransformedAmplitude
        (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
        (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
        (Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
        (Complex.realPhaseIntegrationCoefficientDerivative
          (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
          (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))) x := by
  exact (Complex.hasDerivAt_logarithmicPhaseAdaptedFirstTransform_of_gap
    t a b m hx hgap hlower).continuousAt

theorem Complex.continuousAt_logarithmicPhaseAdaptedSecondTransform_of_gap
    (t : ℝ) (a b m : ℤ) {x gap : ℝ}
    (hx : 0 < x)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousAt
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
          (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))) x := by
  have hfirstDerivative :=
    (Complex.hasDerivAt_logarithmicPhaseAdaptedFirstTransform_of_gap
      t a b m hx hgap hlower).continuousAt
  have hamplitude :=
    (Complex.hasDerivAt_logarithmicPhaseAdaptedCutoffAmplitude a b x).continuousAt
  have hamplitudeDerivative :=
    (Complex.hasDerivAt_logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b x).continuousAt
  have hcoefficient :=
    Complex.continuousAt_logarithmicPhaseAdaptedCoefficient_of_gap
      t m hx hgap hlower
  have hcoefficientDerivative :=
    Complex.continuousAt_logarithmicPhaseAdaptedCoefficientDerivative_of_gap
      t m hx hgap hlower
  have hfirstTransform :=
    Complex.continuousAt_logarithmicPhaseAdaptedFirstTransform_of_gap
      t a b m hx hgap hlower
  unfold Complex.nonstationarySecondTransformedAmplitude
  exact (hfirstDerivative.mul hcoefficient).add
    (hfirstTransform.mul hcoefficientDerivative)

end
end LFunctions
end Boundary
