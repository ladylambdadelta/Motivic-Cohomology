import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.PeriodicBlockPrimitive

/-!
# Local centered integration by parts for the logarithmic phase
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- For the zero Fourier mode, the generic phase-derivative denominator is the
project's logarithmic derivative amplitude. -/
theorem boundaryLineOnePointRealParam_zeroModeDerivativeDenominator_eq_amplitude
    (t : ℝ)
    (a : ℕ)
    (u : ℝ) :
    Complex.realPhaseDerivativeDenominator
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t 0 a)
        u =
      boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u := by
  let speed : ℝ := t / ((a : ℝ) + u)
  have hzeroCast : ((0 : ℤ) : ℝ) = 0 :=
    Int.cast_zero
  have hphaseDerivative :
      boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t 0 a u =
        -speed := by
    unfold boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative
    exact Eq.trans
      (congrArg
        (fun r : ℝ => 2 * Real.pi * r - speed)
        hzeroCast)
      (Eq.trans
        (congrArg (fun r : ℝ => r - speed) (mul_zero (2 * Real.pi)))
        (zero_sub speed))
  have hcastNegative : ((-speed : ℝ) : ℂ) = -(speed : ℂ) :=
    map_neg Complex.ofRealHom speed
  unfold Complex.realPhaseDerivativeDenominator
  unfold boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
  exact Eq.trans
    (congrArg (fun r : ℝ => Complex.I * (r : ℂ)) hphaseDerivative)
    (Eq.trans
      (congrArg (fun z : ℂ => Complex.I * z) hcastNegative)
      (Eq.trans
        (mul_neg Complex.I (speed : ℂ))
        (Eq.trans
          (congrArg Neg.neg (mul_comm Complex.I (speed : ℂ)))
          (Eq.trans
            (mul_neg (speed : ℂ) Complex.I).symm
            rfl))))

/-- The zero-mode logarithmic oscillator has derivative equal to amplitude
times oscillator. -/
theorem hasDerivAt_boundaryLineOnePointRealParam_zeroModeOscillation
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    HasDerivAt
      (Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a))
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u)
      u := by
  have hraw :=
    hasDerivAt_boundaryLineOnePointRealParam_unitBlockModeOscillation
      t 0 ha hu
  have hdenominator :=
    boundaryLineOnePointRealParam_zeroModeDerivativeDenominator_eq_amplitude
      t a u
  have hcoefficient :
      Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u *
        Complex.realPhaseDerivativeDenominator
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t 0 a)
          u =
      boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u :=
    Eq.trans
      (congrArg
        (fun z : ℂ =>
          Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u * z)
        hdenominator)
      (mul_comm _ _)
  exact hraw.congr_deriv hcoefficient

/-- The zero-mode oscillator derivative is interval-integrable on a unit
post-cutoff block. -/
theorem intervalIntegrable_boundaryLineOnePointRealParam_zeroModeOscillationDerivative
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a) :
    IntervalIntegrable
      (fun u : ℝ =>
        boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u)
      volume 0 1 := by
  have hcontinuous :
      ContinuousOn
        (fun u : ℝ =>
          boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u)
        (Set.uIcc (0 : ℝ) 1) := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 :=
      Eq.subst (motive := fun s : Set ℝ => u ∈ s)
        (Set.uIcc_of_le zero_le_one) hu
    have hamplitude :=
      (hasDerivAt_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
        t a
        (boundaryLineOnePointRealParam_unitBlock_coordinate_pos
          t ha huIcc.1)).continuousAt
    have hoscillation :=
      (hasDerivAt_boundaryLineOnePointRealParam_zeroModeOscillation
        t ha huIcc.1).continuousAt
    exact (hamplitude.mul hoscillation).continuousWithinAt
  exact hcontinuous.intervalIntegrable

/-- Local zero-boundary integration by parts for one logarithmic-phase block. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_unitBlock_eq_neg_quadratic
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a) :
    (∫ u in (0 : ℝ)..1,
        Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u *
          ((u - 1 / 2 : ℝ) : ℂ)) =
      -∫ u in (0 : ℝ)..1,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
          eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u := by
  exact
    eulerMaclaurinFirstPeriodicBernoulli_unitBlock_integrationByParts_zeroBoundary
      (Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a))
      (fun u : ℝ =>
        boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u)
      (fun u hu =>
        hasDerivAt_boundaryLineOnePointRealParam_zeroModeOscillation
          t ha
          ((Eq.subst (motive := fun s : Set ℝ => u ∈ s)
            (Set.uIcc_of_le zero_le_one) hu).1))
      (intervalIntegrable_boundaryLineOnePointRealParam_zeroModeOscillationDerivative
        t ha)

end
end LFunctions
end Boundary
