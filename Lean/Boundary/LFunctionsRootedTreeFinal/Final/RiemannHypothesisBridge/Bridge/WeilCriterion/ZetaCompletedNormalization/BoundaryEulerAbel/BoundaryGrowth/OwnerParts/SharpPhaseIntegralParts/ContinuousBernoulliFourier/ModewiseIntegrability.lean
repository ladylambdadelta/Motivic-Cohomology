import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.ModewiseAmplitudeCoefficient

/-!
# Integrability of the global Fourier-mode integration-by-parts data

The modewise integration-by-parts identity is applied once on the whole
translated post-cutoff interval.  This file discharges its analytic
integrability hypotheses directly from the explicit rational formulas.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- The amplitude-bearing reciprocal-coefficient derivative is continuous at
every nonnegative post-cutoff coordinate. -/
theorem continuousAt_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ContinuousAt
      (Complex.realPhaseAmplitudeCoefficientDerivative
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
        (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a))
      u := by
  have hx : 0 < (a : ℝ) + u :=
    boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha hu
  have hx_ne : (a : ℝ) + u ≠ 0 :=
    ne_of_gt hx
  have hshift : ContinuousAt (fun v : ℝ => (a : ℝ) + v) u :=
    continuousAt_const.add continuousAt_id
  have hphaseDerivative :
      ContinuousAt
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
        u := by
    unfold boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative
    exact continuousAt_const.sub
      (continuousAt_const.div hshift hx_ne)
  have hsecondDerivative :
      ContinuousAt
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseSecondDerivative t a)
        u := by
    unfold boundaryLineOnePointRealParam_unitBlockCombinedPhaseSecondDerivative
    exact continuousAt_const.div (hshift.pow 2) (pow_ne_zero 2 hx_ne)
  have hphaseDerivativeComplex :
      ContinuousAt
        (fun v : ℝ =>
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative
            t m a v : ℂ))
        u :=
    Complex.continuous_ofReal.continuousAt.comp' hphaseDerivative
  have hsecondDerivativeComplex :
      ContinuousAt
        (fun v : ℝ =>
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseSecondDerivative
            t a v : ℂ))
        u :=
    Complex.continuous_ofReal.continuousAt.comp hsecondDerivative
  have hdenominator :
      ContinuousAt
        (Complex.realPhaseDerivativeDenominator
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a))
        u := by
    unfold Complex.realPhaseDerivativeDenominator
    exact continuousAt_const.mul hphaseDerivativeComplex
  have hdenominator_ne :
      Complex.realPhaseDerivativeDenominator
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          u ≠ 0 :=
    boundaryLineOnePointRealParam_unitBlockMode_derivativeDenominator_ne_zero
      t hm ha hu
  have hcoefficient :
      ContinuousAt
        (Complex.realPhaseIntegrationCoefficient
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a))
        u := by
    unfold Complex.realPhaseIntegrationCoefficient
    exact hdenominator.inv₀ hdenominator_ne
  have hcoefficientDerivative :
      ContinuousAt
        (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
        u := by
    unfold boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative
    exact
      (continuousAt_const.mul hsecondDerivativeComplex).neg.div
        (hdenominator.pow 2)
        (pow_ne_zero 2 hdenominator_ne)
  have hamplitudeReal :
      ContinuousAt (fun v : ℝ => t / ((a : ℝ) + v)) u :=
    continuousAt_const.div hshift hx_ne
  have hamplitudeRealDerivative :
      ContinuousAt
        (fun v : ℝ => -(t / (((a : ℝ) + v) ^ (2 : ℕ))))
        u :=
    (continuousAt_const.div (hshift.pow 2) (pow_ne_zero 2 hx_ne)).neg
  have hamplitude :
      ContinuousAt
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
        u := by
    unfold boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
    exact
      (Complex.continuous_ofReal.continuousAt.comp hamplitudeReal).mul
        continuousAt_const
  have hamplitudeDerivative :
      ContinuousAt
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
        u := by
    unfold boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
    exact
      (Complex.continuous_ofReal.continuousAt.comp hamplitudeRealDerivative).mul
        continuousAt_const
  unfold Complex.realPhaseAmplitudeCoefficientDerivative
  exact
    (hamplitudeDerivative.mul hcoefficient).add
      (hamplitude.mul hcoefficientDerivative)

/-- The amplitude-bearing coefficient derivative is interval-integrable on
every finite translated post-cutoff interval. -/
theorem intervalIntegrable_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    IntervalIntegrable
      (Complex.realPhaseAmplitudeCoefficientDerivative
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
        (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a))
      volume 0 L := by
  have hcontinuous :
      ContinuousOn
        (Complex.realPhaseAmplitudeCoefficientDerivative
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
          (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a))
        (Set.uIcc 0 L) := by
    intro u hu
    have huIcc : u ∈ Set.Icc 0 L :=
      Eq.subst (motive := fun s : Set ℝ => u ∈ s) (Set.uIcc_of_le hL) hu
    exact
      (continuousAt_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative
        t hm ha huIcc.1).continuousWithinAt
  exact hcontinuous.intervalIntegrable

/-- The derivative of the combined-mode oscillation is continuous at every
nonnegative post-cutoff coordinate. -/
theorem continuousAt_boundaryLineOnePointRealParam_unitBlockModeOscillationDerivative
    (t : ℝ)
    (m : ℤ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ContinuousAt
      (fun v : ℝ =>
        Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) v *
          Complex.realPhaseDerivativeDenominator
            (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
            v)
      u := by
  have hx : 0 < (a : ℝ) + u :=
    boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha hu
  have hphase :=
    hasDerivAt_boundaryLineOnePointRealParam_unitBlockCombinedPhase
      t m a hx
  have hoscillation :
      ContinuousAt
        (Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a))
        u :=
    (Complex.hasDerivAt_realPhaseOscillation hphase).continuousAt
  have hphaseDerivative :=
    hasDerivAt_boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative
      t m a hx
  have hphaseDerivativeComplex :
      ContinuousAt
        (fun v : ℝ =>
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative
            t m a v : ℂ))
        u :=
    Complex.continuous_ofReal.continuousAt.comp'
      hphaseDerivative.continuousAt
  have hdenominator :
      ContinuousAt
        (Complex.realPhaseDerivativeDenominator
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a))
        u := by
    unfold Complex.realPhaseDerivativeDenominator
    exact continuousAt_const.mul hphaseDerivativeComplex
  exact hoscillation.mul hdenominator

/-- The combined-mode oscillation derivative is interval-integrable on every
finite translated post-cutoff interval. -/
theorem intervalIntegrable_boundaryLineOnePointRealParam_unitBlockModeOscillationDerivative
    (t : ℝ)
    (m : ℤ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    IntervalIntegrable
      (fun v : ℝ =>
        Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) v *
          Complex.realPhaseDerivativeDenominator
            (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
            v)
      volume 0 L := by
  have hcontinuous :
      ContinuousOn
        (fun v : ℝ =>
          Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) v *
            Complex.realPhaseDerivativeDenominator
              (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
              v)
        (Set.uIcc 0 L) := by
    intro u hu
    have huIcc : u ∈ Set.Icc 0 L :=
      Eq.subst (motive := fun s : Set ℝ => u ∈ s) (Set.uIcc_of_le hL) hu
    exact
      (continuousAt_boundaryLineOnePointRealParam_unitBlockModeOscillationDerivative
        t m ha huIcc.1).continuousWithinAt
  exact hcontinuous.intervalIntegrable

end
end LFunctions
end Boundary
