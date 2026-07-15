import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.StationaryPhase.MonotoneReciprocalDerivative
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalCentralWindow

/-!
# Exact monotone stationary tails for logarithmic Poisson packets

This file specializes reciprocal-derivative variation to the corrected
logarithmic Fourier phase.  On the left of a stationary center the phase
derivative is negative, so the reciprocal coefficient norm is represented by
the inverse of its negation.  On the right it is positive, so the ordinary
inverse represents the same norm.  These two real functions are respectively
increasing and decreasing, and their derivatives are exactly the norms of the
complex reciprocal-coefficient derivatives, with the appropriate sign.

Keeping these two branches separate avoids differentiating an absolute value
at the stationary point and makes the one-sided van der Corput proof a direct
application of the generic monotone owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

/-- Positive reciprocal derivative gap on the left of the stationary point. -/
def Complex.logarithmicPhaseLeftReciprocalGap
    (t : ℝ) (m : ℤ) (x : ℝ) : ℝ :=
  (-Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹

/-- Positive reciprocal derivative gap on the right of the stationary point. -/
def Complex.logarithmicPhaseRightReciprocalGap
    (t : ℝ) (m : ℤ) (x : ℝ) : ℝ :=
  (Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹

/-- Quotient-rule derivative of the left reciprocal gap. -/
def Complex.logarithmicPhaseLeftReciprocalGapDerivative
    (t : ℝ) (m : ℤ) (x : ℝ) : ℝ :=
  -((-Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2) *
    (-(‖t‖ / x ^ 2))

/-- Quotient-rule derivative of the right reciprocal gap. -/
def Complex.logarithmicPhaseRightReciprocalGapDerivative
    (t : ℝ) (m : ℤ) (x : ℝ) : ℝ :=
  -((Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2) *
    (‖t‖ / x ^ 2)

/-- Algebraic normal form for the derivative of the left reciprocal branch. -/
theorem Complex.logarithmicPhaseLeftReciprocalDerivative_normalForm
    (velocity denominator : ℝ) :
    -(-velocity) / (-denominator) ^ 2 =
      -((-denominator)⁻¹ ^ 2) * (-velocity) := by
  have hinverseSquare :
      ((-denominator) ^ 2)⁻¹ = (-denominator)⁻¹ ^ 2 :=
    (inv_pow (-denominator) 2).symm
  calc
    -(-velocity) / (-denominator) ^ 2 =
        velocity / (-denominator) ^ 2 :=
      congrArg
        (fun numerator : ℝ => numerator / (-denominator) ^ 2)
        (neg_neg velocity)
    _ = velocity * ((-denominator) ^ 2)⁻¹ :=
      div_eq_mul_inv velocity ((-denominator) ^ 2)
    _ = velocity * ((-denominator)⁻¹ ^ 2) :=
      congrArg (fun inverseSquare : ℝ => velocity * inverseSquare)
        hinverseSquare
    _ = ((-denominator)⁻¹ ^ 2) * velocity :=
      mul_comm velocity ((-denominator)⁻¹ ^ 2)
    _ = -((-denominator)⁻¹ ^ 2) * (-velocity) :=
      (neg_mul_neg ((-denominator)⁻¹ ^ 2) velocity).symm

/-- Algebraic normal form for the derivative of the right reciprocal branch. -/
theorem Complex.logarithmicPhaseRightReciprocalDerivative_normalForm
    (velocity denominator : ℝ) :
    (-velocity) / denominator ^ 2 =
      -(denominator⁻¹ ^ 2) * velocity := by
  have hinverseSquare :
      (denominator ^ 2)⁻¹ = denominator⁻¹ ^ 2 :=
    (inv_pow denominator 2).symm
  calc
    (-velocity) / denominator ^ 2 =
        (-velocity) * (denominator ^ 2)⁻¹ :=
      div_eq_mul_inv (-velocity) (denominator ^ 2)
    _ = (-velocity) * (denominator⁻¹ ^ 2) :=
      congrArg (fun inverseSquare : ℝ => (-velocity) * inverseSquare)
        hinverseSquare
    _ = (denominator⁻¹ ^ 2) * (-velocity) :=
      mul_comm (-velocity) (denominator⁻¹ ^ 2)
    _ = -(denominator⁻¹ ^ 2 * velocity) :=
      mul_neg (denominator⁻¹ ^ 2) velocity
    _ = -(denominator⁻¹ ^ 2) * velocity :=
      (neg_mul (denominator⁻¹ ^ 2) velocity).symm

/-- Negating the logarithmic Fourier derivative negates its velocity. -/
theorem Complex.hasDerivAt_neg_logarithmicPhaseFourierTwistedDerivative
    (t : ℝ) (ht_nonneg : 0 ≤ t) (m : ℤ)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ =>
        -Complex.logarithmicPhaseFourierTwistedDerivative t m y)
      (-(‖t‖ / x ^ 2)) x := by
  exact
    (Complex.logarithmicPhaseFourierTwistedDerivative_hasDerivAt
      t ht_nonneg m hx).neg

/-- Differential formula for the left reciprocal gap. -/
theorem Complex.hasDerivAt_logarithmicPhaseLeftReciprocalGap
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (m : ℤ) {x : ℝ} (hx : 0 < x)
    (hcenter :
      x < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    HasDerivAt
      (Complex.logarithmicPhaseLeftReciprocalGap t m)
      (Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x) x := by
  have hstationary :
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m :=
    ne_of_lt hcenter
  have hdenominator :
      Complex.logarithmicPhaseFourierTwistedDerivative t m x ≠ 0 := by
    have hcomplex :=
      Complex.logarithmicPhaseFourierDerivativeDenominator_ne_zero
        t ht ht_nonneg m hx hstationary
    intro hzero
    have hofRealZero :
        ((Complex.logarithmicPhaseFourierTwistedDerivative t m x : ℝ) : ℂ) =
          0 :=
      congrArg (fun value : ℝ => (value : ℂ)) hzero
    have hproductZero :
        Complex.I *
            (Complex.logarithmicPhaseFourierTwistedDerivative t m x : ℂ) =
          0 :=
      (congrArg (fun value : ℂ => Complex.I * value) hofRealZero).trans
        (mul_zero Complex.I)
    exact hcomplex hproductZero
  have hnegativeDenominator :
      -Complex.logarithmicPhaseFourierTwistedDerivative t m x ≠ 0 :=
    neg_ne_zero.mpr hdenominator
  have hbase :=
    Complex.hasDerivAt_neg_logarithmicPhaseFourierTwistedDerivative
      t ht_nonneg m hx
  have hinverse := hbase.inv hnegativeDenominator
  have hderivative :
      - -(‖t‖ / x ^ 2) /
          (-Complex.logarithmicPhaseFourierTwistedDerivative t m x) ^ 2 =
      -((-Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2) *
          (-(‖t‖ / x ^ 2)) :=
    Complex.logarithmicPhaseLeftReciprocalDerivative_normalForm
      (‖t‖ / x ^ 2)
      (Complex.logarithmicPhaseFourierTwistedDerivative t m x)
  unfold Complex.logarithmicPhaseLeftReciprocalGap
  unfold Complex.logarithmicPhaseLeftReciprocalGapDerivative
  change HasDerivAt
    (fun y : ℝ => (-Complex.logarithmicPhaseFourierTwistedDerivative t m y)⁻¹)
    (-((-Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2) *
      (-(‖t‖ / x ^ 2))) x
  exact Eq.subst
    (motive := fun derivative : ℝ =>
      HasDerivAt
        (fun y : ℝ => (-Complex.logarithmicPhaseFourierTwistedDerivative t m y)⁻¹)
        derivative x)
    hderivative hinverse

/-- Differential formula for the right reciprocal gap. -/
theorem Complex.hasDerivAt_logarithmicPhaseRightReciprocalGap
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (m : ℤ) {x : ℝ} (hx : 0 < x)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < x) :
    HasDerivAt
      (Complex.logarithmicPhaseRightReciprocalGap t m)
      (Complex.logarithmicPhaseRightReciprocalGapDerivative t m x) x := by
  have hstationary :
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m :=
    ne_of_gt hcenter
  have hdenominator :
      Complex.logarithmicPhaseFourierTwistedDerivative t m x ≠ 0 := by
    have hcomplex :=
      Complex.logarithmicPhaseFourierDerivativeDenominator_ne_zero
        t ht ht_nonneg m hx hstationary
    intro hzero
    have hofRealZero :
        ((Complex.logarithmicPhaseFourierTwistedDerivative t m x : ℝ) : ℂ) =
          0 :=
      congrArg (fun value : ℝ => (value : ℂ)) hzero
    have hproductZero :
        Complex.I *
            (Complex.logarithmicPhaseFourierTwistedDerivative t m x : ℂ) =
          0 :=
      (congrArg (fun value : ℂ => Complex.I * value) hofRealZero).trans
        (mul_zero Complex.I)
    exact hcomplex hproductZero
  have hbase :=
    Complex.logarithmicPhaseFourierTwistedDerivative_hasDerivAt
      t ht_nonneg m hx
  have hinverse := hbase.inv hdenominator
  have hderivative :
      -(‖t‖ / x ^ 2) /
          (Complex.logarithmicPhaseFourierTwistedDerivative t m x) ^ 2 =
        -((Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2) *
          (‖t‖ / x ^ 2) :=
    Complex.logarithmicPhaseRightReciprocalDerivative_normalForm
      (‖t‖ / x ^ 2)
      (Complex.logarithmicPhaseFourierTwistedDerivative t m x)
  unfold Complex.logarithmicPhaseRightReciprocalGap
  unfold Complex.logarithmicPhaseRightReciprocalGapDerivative
  change HasDerivAt
    (fun y : ℝ => (Complex.logarithmicPhaseFourierTwistedDerivative t m y)⁻¹)
    (-((Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2) *
      (‖t‖ / x ^ 2)) x
  exact Eq.subst
    (motive := fun derivative : ℝ =>
      HasDerivAt
        (fun y : ℝ => (Complex.logarithmicPhaseFourierTwistedDerivative t m y)⁻¹)
        derivative x)
    hderivative hinverse

/-- The logarithmic Fourier derivative is negative to the left of a negative
mode's stationary point. -/
theorem Complex.logarithmicPhaseFourierTwistedDerivative_neg_left
    (t : ℝ) (ht : 1 ≤ ‖t‖) (m : ℤ) (hm : m < 0)
    {x : ℝ} (hx : 0 < x)
    (hcenter :
      x < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    Complex.logarithmicPhaseFourierTwistedDerivative t m x < 0 := by
  exact
    Complex.logarithmicPhaseFourierTwistedDerivative_neg_of_lt_stationaryPoint
      t hm hx hcenter

/-- The logarithmic Fourier derivative is positive to the right of a negative
mode's stationary point. -/
theorem Complex.logarithmicPhaseFourierTwistedDerivative_pos_right
    (t : ℝ) (ht : 1 ≤ ‖t‖) (m : ℤ) (hm : m < 0)
    {x : ℝ} (hx : 0 < x)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < x) :
    0 < Complex.logarithmicPhaseFourierTwistedDerivative t m x := by
  exact
    Complex.logarithmicPhaseFourierTwistedDerivative_pos_of_gt_stationaryPoint
      t hm hx hcenter

/-- On the left branch, the real reciprocal gap equals the norm of the
complex integration coefficient. -/
theorem Complex.logarithmicPhaseLeftReciprocalGap_eq_coefficientNorm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (m : ℤ) (hm : m < 0)
    {x : ℝ} (hx : 0 < x)
    (hcenter :
      x < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    Complex.logarithmicPhaseLeftReciprocalGap t m x =
      ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ := by
  have hnegative :=
    Complex.logarithmicPhaseFourierTwistedDerivative_neg_left
      t ht m hm hx hcenter
  have habs :
      ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ =
        -Complex.logarithmicPhaseFourierTwistedDerivative t m x :=
    Real.norm_of_nonpos (le_of_lt hnegative)
  have hcoefficientNorm :=
    Complex.norm_realPhaseIntegrationCoefficient
      (Complex.logarithmicPhaseFourierTwistedDerivative t m) x
  exact
    (congrArg Inv.inv habs).symm.trans hcoefficientNorm.symm

/-- On the right branch, the real reciprocal gap equals the norm of the
complex integration coefficient. -/
theorem Complex.logarithmicPhaseRightReciprocalGap_eq_coefficientNorm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (m : ℤ) (hm : m < 0)
    {x : ℝ} (hx : 0 < x)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < x) :
    Complex.logarithmicPhaseRightReciprocalGap t m x =
      ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ := by
  have hpositive :=
    Complex.logarithmicPhaseFourierTwistedDerivative_pos_right
      t ht m hm hx hcenter
  have habs :
      ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ =
        Complex.logarithmicPhaseFourierTwistedDerivative t m x :=
    Real.norm_of_nonneg (le_of_lt hpositive)
  have hcoefficientNorm :=
    Complex.norm_realPhaseIntegrationCoefficient
      (Complex.logarithmicPhaseFourierTwistedDerivative t m) x
  exact
    (congrArg Inv.inv habs).symm.trans hcoefficientNorm.symm

/-- The left reciprocal-gap derivative is nonnegative. -/
theorem Complex.logarithmicPhaseLeftReciprocalGapDerivative_nonneg
    (t : ℝ) (m : ℤ) (x : ℝ) :
    0 ≤ Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x := by
  unfold Complex.logarithmicPhaseLeftReciprocalGapDerivative
  have hsquare :
      0 ≤
        (-Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2 :=
    sq_nonneg _
  have hvelocity : 0 ≤ ‖t‖ / x ^ 2 :=
    div_nonneg (norm_nonneg t) (sq_nonneg x)
  have hnegativeSquare :
      -((-Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2) ≤ 0 :=
    neg_nonpos.mpr hsquare
  have hnegativeVelocity : -(‖t‖ / x ^ 2) ≤ 0 :=
    neg_nonpos.mpr hvelocity
  exact mul_nonneg_of_nonpos_of_nonpos hnegativeSquare hnegativeVelocity

/-- The right reciprocal-gap derivative is nonpositive. -/
theorem Complex.logarithmicPhaseRightReciprocalGapDerivative_nonpos
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.logarithmicPhaseRightReciprocalGapDerivative t m x ≤ 0 := by
  unfold Complex.logarithmicPhaseRightReciprocalGapDerivative
  have hsquare :
      0 ≤
        (Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2 :=
    sq_nonneg _
  have hnegativeSquare :
      -((Complex.logarithmicPhaseFourierTwistedDerivative t m x)⁻¹ ^ 2) ≤ 0 :=
    neg_nonpos.mpr hsquare
  have hvelocity : 0 ≤ ‖t‖ / x ^ 2 :=
    div_nonneg (norm_nonneg t) (sq_nonneg x)
  exact mul_nonpos_of_nonpos_of_nonneg hnegativeSquare hvelocity

/-- Absolute value of the left reciprocal derivative removes no sign. -/
theorem Complex.abs_logarithmicPhaseLeftReciprocalGapDerivative
    (t : ℝ) (m : ℤ) (x : ℝ) :
    |Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x| =
      Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x :=
  abs_of_nonneg
    (Complex.logarithmicPhaseLeftReciprocalGapDerivative_nonneg t m x)

/-- Absolute value of the right reciprocal derivative removes its minus sign. -/
theorem Complex.abs_logarithmicPhaseRightReciprocalGapDerivative
    (t : ℝ) (m : ℤ) (x : ℝ) :
    |Complex.logarithmicPhaseRightReciprocalGapDerivative t m x| =
      -Complex.logarithmicPhaseRightReciprocalGapDerivative t m x :=
  abs_of_nonpos
    (Complex.logarithmicPhaseRightReciprocalGapDerivative_nonpos t m x)

end

end LFunctions
end Boundary
