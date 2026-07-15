import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.ModewiseReciprocalCoefficient

/-!
# Amplitude-bearing reciprocal coefficient for a Fourier mode

This file combines the logarithmic derivative amplitude with the reciprocal
combined-phase coefficient and records its inverse-square derivative bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The generic product-rule theorem specializes to the logarithmic amplitude
and combined Fourier phase. -/
theorem hasDerivAt_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficient
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    HasDerivAt
      (Complex.realPhaseAmplitudeCoefficient
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a))
      (Complex.realPhaseAmplitudeCoefficientDerivative
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
        (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
        u)
      u := by
  have hx : 0 < (a : ℝ) + u :=
    boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha hu
  have hamplitude :=
    hasDerivAt_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
      t a hx
  have hcoefficient :=
    hasDerivAt_boundaryLineOnePointRealParam_unitBlockModeCoefficient
      t hm ha hu
  exact Complex.hasDerivAt_realPhaseAmplitudeCoefficient
    (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
    (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
    (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
    (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
    u hamplitude hcoefficient

/-- The amplitude-bearing coefficient derivative is bounded pointwise by two
copies of the translated inverse-square density. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative_le_inverseSquare
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ‖Complex.realPhaseAmplitudeCoefficientDerivative
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
        (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
        u‖ ≤
      ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)) +
        ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)) := by
  let M : ℝ := ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ))
  let amplitude :=
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a
  let amplitudeDerivative :=
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a
  let phaseDerivative :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a
  let coefficientDerivative :=
    boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a
  have hx : 0 < (a : ℝ) + u :=
    boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha hu
  have hM : 0 ≤ M :=
    div_nonneg (norm_nonneg t) (le_of_lt (sq_pos_of_pos hx))
  have hamplitude : ‖amplitude u‖ ≤ 1 :=
    norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude_le_one
      t ha hu
  have hamplitudeDerivative : ‖amplitudeDerivative u‖ ≤ M :=
    le_of_eq
      (norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative_eq_inverseSquare
        t a hx)
  have hcoefficient :
      ‖Complex.realPhaseIntegrationCoefficient phaseDerivative u‖ ≤ 1 :=
    norm_boundaryLineOnePointRealParam_unitBlockModeCoefficient_le_one
      t hm ha hu
  have hcoefficientDerivative : ‖coefficientDerivative u‖ ≤ M :=
    norm_boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative_le_inverseSquare
      t hm ha hu
  have hfirst :
      ‖amplitudeDerivative u *
          Complex.realPhaseIntegrationCoefficient phaseDerivative u‖ ≤ M :=
    le_trans
      (le_of_eq
        (norm_mul
          (amplitudeDerivative u)
          (Complex.realPhaseIntegrationCoefficient phaseDerivative u)))
      (le_trans
        (mul_le_mul hamplitudeDerivative hcoefficient
          (norm_nonneg
            (Complex.realPhaseIntegrationCoefficient phaseDerivative u)) hM)
        (le_of_eq (mul_one M)))
  have hsecond : ‖amplitude u * coefficientDerivative u‖ ≤ M :=
    le_trans
      (le_of_eq (norm_mul (amplitude u) (coefficientDerivative u)))
      (le_trans
        (mul_le_mul hamplitude hcoefficientDerivative
          (norm_nonneg (coefficientDerivative u)) zero_le_one)
        (le_of_eq (one_mul M)))
  exact le_trans
    (norm_add_le _ _)
    (add_le_add hfirst hsecond)

/-- The derivative of the amplitude-bearing reciprocal coefficient is bounded
by two copies of the inverse-square majorant. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative_le
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ‖Complex.realPhaseAmplitudeCoefficientDerivative
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
        (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
        u‖ ≤
      ‖t‖ / ((a : ℝ) ^ (2 : ℕ)) +
        ‖t‖ / ((a : ℝ) ^ (2 : ℕ)) := by
  let M : ℝ := ‖t‖ / ((a : ℝ) ^ (2 : ℕ))
  let amplitude :=
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a
  let amplitudeDerivative :=
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a
  let phaseDerivative :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a
  let coefficientDerivative :=
    boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a
  have hM : 0 ≤ M :=
    div_nonneg (norm_nonneg t) (sq_nonneg (a : ℝ))
  have hamplitude : ‖amplitude u‖ ≤ 1 :=
    norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude_le_one
      t ha hu
  have hamplitudeDerivative : ‖amplitudeDerivative u‖ ≤ M :=
    norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative_le
      t ha hu
  have hcoefficient :
      ‖Complex.realPhaseIntegrationCoefficient phaseDerivative u‖ ≤ 1 :=
    norm_boundaryLineOnePointRealParam_unitBlockModeCoefficient_le_one
      t hm ha hu
  have hcoefficientDerivative : ‖coefficientDerivative u‖ ≤ M :=
    norm_boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative_le
      t hm ha hu
  have hfirst :
      ‖amplitudeDerivative u *
          Complex.realPhaseIntegrationCoefficient phaseDerivative u‖ ≤
        M := by
    have hproduct :=
      mul_le_mul
        hamplitudeDerivative
        hcoefficient
        (norm_nonneg
          (Complex.realPhaseIntegrationCoefficient phaseDerivative u))
        hM
    exact le_trans
      (le_of_eq
        (norm_mul
          (amplitudeDerivative u)
          (Complex.realPhaseIntegrationCoefficient phaseDerivative u)))
      (le_trans hproduct (le_of_eq (mul_one M)))
  have hsecond :
      ‖amplitude u * coefficientDerivative u‖ ≤ M := by
    have hproduct :=
      mul_le_mul
        hamplitude
        hcoefficientDerivative
        (norm_nonneg (coefficientDerivative u))
        zero_le_one
    exact le_trans
      (le_of_eq (norm_mul (amplitude u) (coefficientDerivative u)))
      (le_trans hproduct (le_of_eq (one_mul M)))
  have htriangle :
      ‖amplitudeDerivative u *
            Complex.realPhaseIntegrationCoefficient phaseDerivative u +
          amplitude u * coefficientDerivative u‖ ≤
        ‖amplitudeDerivative u *
            Complex.realPhaseIntegrationCoefficient phaseDerivative u‖ +
          ‖amplitude u * coefficientDerivative u‖ :=
    norm_add_le _ _
  exact le_trans htriangle (add_le_add hfirst hsecond)

/-- The combined real-phase oscillation has the derivative expected by the
generic nonstationary integration-by-parts theorem. -/
theorem hasDerivAt_boundaryLineOnePointRealParam_unitBlockModeOscillation
    (t : ℝ)
    (m : ℤ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    HasDerivAt
      (Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a))
      (Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u *
        Complex.realPhaseDerivativeDenominator
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          u)
      u := by
  have hx : 0 < (a : ℝ) + u :=
    boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha hu
  have hphase :=
    hasDerivAt_boundaryLineOnePointRealParam_unitBlockCombinedPhase
      t m a hx
  exact Complex.hasDerivAt_realPhaseOscillation hphase

/-- The amplitude-bearing reciprocal coefficient has norm at most one at
every post-cutoff point. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficient_le_one
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ‖Complex.realPhaseAmplitudeCoefficient
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
        u‖ ≤ 1 := by
  have hamplitude :=
    norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude_le_one
      t ha hu
  have hcoefficient :=
    norm_boundaryLineOnePointRealParam_unitBlockModeCoefficient_le_one
      t hm ha hu
  have hproduct :=
    mul_le_mul
      hamplitude
      hcoefficient
      (norm_nonneg
        (Complex.realPhaseIntegrationCoefficient
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          u))
      zero_le_one
  exact le_trans
    (le_of_eq
      (norm_mul
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u)
        (Complex.realPhaseIntegrationCoefficient
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          u)))
    (le_trans hproduct (le_of_eq (one_mul 1)))

end
end LFunctions
end Boundary
