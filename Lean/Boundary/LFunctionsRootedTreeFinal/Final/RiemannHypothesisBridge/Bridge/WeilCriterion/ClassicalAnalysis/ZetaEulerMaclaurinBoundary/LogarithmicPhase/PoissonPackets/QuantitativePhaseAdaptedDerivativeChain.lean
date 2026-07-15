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

theorem Complex.continuousAt_logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative
    (a b : ℤ) (x : ℝ) :
    ContinuousAt
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b) x := by
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative
  have hreal : ContinuousAt
      (Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b) x :=
    (Real.contDiff_quantitativeLogarithmicBlockCutoffSecondDerivative a b).continuous.continuousAt
  exact Complex.continuous_ofReal.continuousAt.comp hreal

theorem Complex.continuousAt_logarithmicPhaseAdaptedTwistedPhaseThirdDerivative
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt
      (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t) x := by
  unfold Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative
  have hxne : x ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hx)
  have hnumerator : ContinuousAt (fun _ : ℝ => 2 * ‖t‖) x :=
    continuousAt_const
  have hdenominator : ContinuousAt (fun y : ℝ => y ^ 3) x :=
    continuousAt_id.pow 3
  have hquotient : ContinuousAt (fun y : ℝ => 2 * ‖t‖ / y ^ 3) x :=
    hnumerator.div hdenominator hxne
  exact hquotient.neg

theorem Complex.continuousAt_logarithmicPhaseAdaptedCoefficientSecondDerivative_of_gap
    (t : ℝ) (m : ℤ) {x gap : ℝ}
    (hx : 0 < x)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousAt
      (Complex.realPhaseIntegrationCoefficientSecondDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t)) x := by
  have hfirst : ContinuousAt
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x :=
    (Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhaseDerivative
      t m hx).continuousAt
  have hsecond : ContinuousAt
      (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t) x :=
    (Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhaseSecondDerivative
      t hx).continuousAt
  have hthird : ContinuousAt
      (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t) x :=
    Complex.continuousAt_logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t hx
  have hdenominator : ContinuousAt
      (Complex.realPhaseDerivativeDenominator
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)) x := by
    unfold Complex.realPhaseDerivativeDenominator
    exact continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp hfirst)
  have hdenominator_ne :
      Complex.realPhaseDerivativeDenominator
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x ≠ 0 :=
    Complex.logarithmicPhaseAdaptedDerivativeDenominator_ne_zero_of_gap
      t m x gap hgap hlower
  have hthirdComplex : ContinuousAt
      (fun y : ℝ => (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t y : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp hthird
  have hsecondComplex : ContinuousAt
      (fun y : ℝ => (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t y : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp hsecond
  unfold Complex.realPhaseIntegrationCoefficientSecondDerivative
  have hleftNumerator : ContinuousAt
      (fun y : ℝ => -(Complex.I *
        (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t y : ℂ))) x :=
    (continuousAt_const.mul hthirdComplex).neg
  have hleft := hleftNumerator.div (hdenominator.pow 2)
    (pow_ne_zero 2 hdenominator_ne)
  have hrightNumerator : ContinuousAt
      (fun y : ℝ => 2 * (Complex.I *
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t y : ℂ)) ^ 2) x :=
    continuousAt_const.mul
      ((continuousAt_const.mul hsecondComplex).pow 2)
  have hright := hrightNumerator.div (hdenominator.pow 3)
    (pow_ne_zero 3 hdenominator_ne)
  exact hleft.add hright

theorem Complex.continuousAt_logarithmicPhaseAdaptedFirstTransformDerivative_of_gap
    (t : ℝ) (a b m : ℤ) {x gap : ℝ}
    (hx : 0 < x)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ContinuousAt
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
          (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t))) x := by
  have hamplitude :=
    (Complex.hasDerivAt_logarithmicPhaseAdaptedCutoffAmplitude a b x).continuousAt
  have hamplitudeDerivative :=
    (Complex.hasDerivAt_logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b x).continuousAt
  have hamplitudeSecond :=
    Complex.continuousAt_logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b x
  have hcoefficient :=
    Complex.continuousAt_logarithmicPhaseAdaptedCoefficient_of_gap
      t m hx hgap hlower
  have hcoefficientDerivative :=
    Complex.continuousAt_logarithmicPhaseAdaptedCoefficientDerivative_of_gap
      t m hx hgap hlower
  have hcoefficientSecond :=
    Complex.continuousAt_logarithmicPhaseAdaptedCoefficientSecondDerivative_of_gap
      t m hx hgap hlower
  unfold Complex.nonstationaryFirstTransformedDerivativeExplicit
  have hfirst := hamplitudeSecond.mul hcoefficient
  have htwo : ContinuousAt (fun _ : ℝ => (2 : ℂ)) x :=
    continuousAt_const
  have hmiddle :=
    (htwo.mul hamplitudeDerivative).mul
      hcoefficientDerivative
  have hlast := hamplitude.mul hcoefficientSecond
  exact (hfirst.add hmiddle).add hlast

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
    Complex.continuousAt_logarithmicPhaseAdaptedFirstTransformDerivative_of_gap
      t a b m hx hgap hlower
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
