import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.LocalCenteredIntegrationByParts

/-!
# Centered decomposition of the local Bernoulli integral

This file separates the zero-endpoint quadratic primitive into its periodic
centered part and the exact Bernoulli moment `1/12`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- Complexification of the centered quadratic Bernoulli primitive. -/
noncomputable def eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex
    (u : ℝ) : ℂ :=
  (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u : ℂ)

/-- The complex zero-endpoint primitive is the centered primitive minus its
Bernoulli moment. -/
theorem eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex_eq_centered_sub
    (u : ℝ) :
    eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u =
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u -
        (1 / 12 : ℂ) := by
  have hreal :
      eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u =
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u -
          (1 / 12 : ℝ) :=
    (add_sub_cancel_right
      (eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u)
      (1 / 12 : ℝ)).symm
  have hcast :
      (eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u : ℂ) =
        ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u -
          (1 / 12 : ℝ) : ℝ) : ℂ) :=
    congrArg (fun r : ℝ => (r : ℂ)) hreal
  have hcastSub :
      ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u -
          (1 / 12 : ℝ) : ℝ) : ℂ) =
        (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u : ℂ) -
          (1 / 12 : ℂ) :=
    Eq.trans
      (map_sub Complex.ofRealHom
        (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u)
        (1 / 12 : ℝ))
      (congrArg
        (fun z : ℂ =>
          (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u : ℂ) - z)
        (Complex.ofReal_div (1 : ℝ) (12 : ℝ)))
  unfold eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex
  unfold eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex
  exact Eq.trans hcast hcastSub

/-- The centered quadratic polynomial is continuous after complexification. -/
theorem continuous_eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex :
    Continuous
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex := by
  have hreal :
      Continuous
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive :=
    continuous_iff_continuousAt.mpr
      (fun u =>
        (hasDerivAt_eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive
          u).continuousAt)
  exact Complex.continuous_ofReal.comp hreal

/-- The oscillator derivative times the centered primitive is integrable on a
post-cutoff unit block. -/
theorem intervalIntegrable_boundaryLineOnePointRealParam_zeroModeDerivative_mul_centeredPrimitive
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a) :
    IntervalIntegrable
      (fun u : ℝ =>
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
          eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u)
      volume 0 1 := by
  have hderivative :
      IntervalIntegrable
        (fun u : ℝ =>
          boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u)
        volume 0 1 :=
    intervalIntegrable_boundaryLineOnePointRealParam_zeroModeOscillationDerivative
      t ha
  have hcenteredContinuous :
      ContinuousOn
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex
        (Set.uIcc (0 : ℝ) 1) :=
    continuous_eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex.continuousOn
  exact hderivative.mul_continuousOn hcenteredContinuous

/-- The oscillator derivative times the constant Bernoulli moment is
interval-integrable. -/
theorem intervalIntegrable_boundaryLineOnePointRealParam_zeroModeDerivative_mul_oneTwelfth
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a) :
    IntervalIntegrable
      (fun u : ℝ =>
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
          (1 / 12 : ℂ))
      volume 0 1 := by
  exact
    (intervalIntegrable_boundaryLineOnePointRealParam_zeroModeOscillationDerivative
      t ha).mul_const (1 / 12 : ℂ)

/-- On one post-cutoff block, the first Bernoulli integral is the negative
centered contribution plus the exact constant-moment contribution. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_unitBlock_eq_neg_centered_add_constant
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a) :
    (∫ u in (0 : ℝ)..1,
        Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u *
          ((u - 1 / 2 : ℝ) : ℂ)) =
      -(∫ u in (0 : ℝ)..1,
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
            eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u) +
        ∫ u in (0 : ℝ)..1,
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
            (1 / 12 : ℂ) := by
  let derivative : ℝ → ℂ := fun u =>
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
      Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u
  have hlocal :
      (∫ u in (0 : ℝ)..1,
          Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u *
            ((u - 1 / 2 : ℝ) : ℂ)) =
        -(∫ u in (0 : ℝ)..1,
            derivative u *
              eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_unitBlock_eq_neg_quadratic
      t ha
  have hpointwise :
      (fun u : ℝ =>
        derivative u *
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u) =
        (fun u : ℝ =>
          derivative u *
              eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u -
            derivative u * (1 / 12 : ℂ)) := by
    funext u
    exact Eq.trans
      (congrArg (fun z : ℂ => derivative u * z)
        (eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex_eq_centered_sub u))
      (mul_sub (derivative u)
        (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u)
        (1 / 12 : ℂ))
  have hcentered :
      IntervalIntegrable
        (fun u : ℝ =>
          derivative u *
            eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u)
        volume 0 1 :=
    intervalIntegrable_boundaryLineOnePointRealParam_zeroModeDerivative_mul_centeredPrimitive
      t ha
  have hconstant :
      IntervalIntegrable
        (fun u : ℝ => derivative u * (1 / 12 : ℂ))
        volume 0 1 :=
    intervalIntegrable_boundaryLineOnePointRealParam_zeroModeDerivative_mul_oneTwelfth
      t ha
  have hintegralSplit :
      (∫ u in (0 : ℝ)..1,
          derivative u *
            eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u) =
        (∫ u in (0 : ℝ)..1,
            derivative u *
              eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u) -
          ∫ u in (0 : ℝ)..1, derivative u * (1 / 12 : ℂ) := by
    exact Eq.trans
      (intervalIntegral.integral_congr
        (fun u _hu => congrFun hpointwise u))
      (intervalIntegral.integral_sub hcentered hconstant)
  let centeredIntegral : ℂ :=
    ∫ u in (0 : ℝ)..1,
      derivative u *
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u
  let constantIntegral : ℂ :=
    ∫ u in (0 : ℝ)..1, derivative u * (1 / 12 : ℂ)
  have hnegativeDifference :
      -(centeredIntegral - constantIntegral) =
        -centeredIntegral + constantIntegral := by
    exact Eq.trans
      (neg_sub centeredIntegral constantIntegral)
      (Eq.trans
        (sub_eq_add_neg constantIntegral centeredIntegral)
        (add_comm constantIntegral (-centeredIntegral)))
  exact Eq.trans hlocal
    (Eq.trans
      (congrArg Neg.neg hintegralSplit)
      hnegativeDifference)

end
end LFunctions
end Boundary
