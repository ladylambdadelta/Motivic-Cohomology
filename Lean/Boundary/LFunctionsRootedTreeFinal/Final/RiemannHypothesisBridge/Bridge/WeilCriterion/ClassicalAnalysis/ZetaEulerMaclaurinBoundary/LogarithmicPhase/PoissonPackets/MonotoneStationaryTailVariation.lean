import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.MonotoneStationaryTails
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.Reconstruction

/-!
# Reciprocal-gap variation identities for logarithmic packets

This file normalizes the real quotient-rule derivatives from
`MonotoneStationaryTails` against the norm formula for the complex
integration-coefficient derivative.  It then supplies interval integrability
and exact total-variation identities on each side of a stationary point.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

/-- Squaring the inverse of a negated real number removes the sign. -/
theorem Real.inv_neg_sq_eq_inv_sq
    (x : ℝ) :
    (-x)⁻¹ ^ 2 = x⁻¹ ^ 2 := by
  have hinverse : (-x)⁻¹ = -(x⁻¹) :=
    (inv_neg : (-x : ℝ)⁻¹ = -(x⁻¹))
  exact
    (congrArg (fun value : ℝ => value ^ 2) hinverse).trans
      (neg_sq (x⁻¹))

/-- The square of a real norm is the ordinary square. -/
theorem Real.norm_sq_eq_sq
    (x : ℝ) :
    ‖x‖ ^ 2 = x ^ 2 := by
  have hnorm : ‖x‖ = |x| :=
    Real.norm_eq_abs x
  exact
    (congrArg (fun value : ℝ => value ^ 2) hnorm).trans
      (sq_abs x)

/-- Squared inverse is inverse squared. -/
theorem Real.inv_sq_eq_sq_inv
    (x : ℝ) :
    x⁻¹ ^ 2 = (x ^ 2)⁻¹ :=
  inv_pow x 2

/-- Inverse square can be expressed using the square of the norm. -/
theorem Real.inv_sq_eq_norm_sq_inv
    (x : ℝ) :
    x⁻¹ ^ 2 = (‖x‖ ^ 2)⁻¹ := by
  exact
    (Real.inv_sq_eq_sq_inv x).trans
      (congrArg Inv.inv (Real.norm_sq_eq_sq x).symm)

/-- Multiplication by an inverse denominator is division. -/
theorem Real.mul_norm_sq_inv_eq_div
    (numerator denominator : ℝ) :
    numerator * (‖denominator‖ ^ 2)⁻¹ =
      numerator / ‖denominator‖ ^ 2 :=
  (div_eq_mul_inv numerator (‖denominator‖ ^ 2)).symm

/-- Move a squared inverse from the left of a product to the right. -/
theorem Real.inv_sq_mul_eq_mul_inv_sq
    (denominator numerator : ℝ) :
    denominator⁻¹ ^ 2 * numerator =
      numerator * denominator⁻¹ ^ 2 :=
  mul_comm (denominator⁻¹ ^ 2) numerator

/-- The left quotient-rule expression is the positive reciprocal-curvature
density. -/
theorem Real.neg_inv_neg_sq_mul_neg_eq_div_norm_sq
    (denominator numerator : ℝ) :
    -((-denominator)⁻¹ ^ 2) * (-numerator) =
      numerator / ‖denominator‖ ^ 2 := by
  have hremove_outer_signs :
      -((-denominator)⁻¹ ^ 2) * (-numerator) =
        (-denominator)⁻¹ ^ 2 * numerator :=
    neg_mul_neg ((-denominator)⁻¹ ^ 2) numerator
  have hremove_inner_sign :
      (-denominator)⁻¹ ^ 2 * numerator =
        denominator⁻¹ ^ 2 * numerator :=
    congrArg
      (fun value : ℝ => value * numerator)
      (Real.inv_neg_sq_eq_inv_sq denominator)
  have hcommute :
      denominator⁻¹ ^ 2 * numerator =
        numerator * denominator⁻¹ ^ 2 :=
    Real.inv_sq_mul_eq_mul_inv_sq denominator numerator
  have hnorm_inverse :
      numerator * denominator⁻¹ ^ 2 =
        numerator * (‖denominator‖ ^ 2)⁻¹ :=
    congrArg
      (fun value : ℝ => numerator * value)
      (Real.inv_sq_eq_norm_sq_inv denominator)
  exact
    hremove_outer_signs.trans
      (hremove_inner_sign.trans
        (hcommute.trans
          (hnorm_inverse.trans
            (Real.mul_norm_sq_inv_eq_div numerator denominator))))

/-- The right quotient-rule expression is the negative reciprocal-curvature
density. -/
theorem Real.neg_inv_sq_mul_eq_neg_div_norm_sq
    (denominator numerator : ℝ) :
    -(denominator⁻¹ ^ 2) * numerator =
      -(numerator / ‖denominator‖ ^ 2) := by
  have hnegativeProduct :
      -(denominator⁻¹ ^ 2) * numerator =
        -(denominator⁻¹ ^ 2 * numerator) :=
    neg_mul (denominator⁻¹ ^ 2) numerator
  have hcommute :
      denominator⁻¹ ^ 2 * numerator =
        numerator * denominator⁻¹ ^ 2 :=
    Real.inv_sq_mul_eq_mul_inv_sq denominator numerator
  have hnormInverse :
      numerator * denominator⁻¹ ^ 2 =
        numerator * (‖denominator‖ ^ 2)⁻¹ :=
    congrArg
      (fun value : ℝ => numerator * value)
      (Real.inv_sq_eq_norm_sq_inv denominator)
  have hdivision :
      numerator * (‖denominator‖ ^ 2)⁻¹ =
        numerator / ‖denominator‖ ^ 2 :=
    Real.mul_norm_sq_inv_eq_div numerator denominator
  exact
    hnegativeProduct.trans
      (congrArg Neg.neg
        (hcommute.trans (hnormInverse.trans hdivision)))

/-- Exact positive density represented by the left reciprocal-gap derivative. -/
theorem Complex.logarithmicPhaseLeftReciprocalGapDerivative_eq_density
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x =
      (‖t‖ / x ^ 2) /
        ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ ^ 2 := by
  unfold Complex.logarithmicPhaseLeftReciprocalGapDerivative
  exact
    Real.neg_inv_neg_sq_mul_neg_eq_div_norm_sq
      (Complex.logarithmicPhaseFourierTwistedDerivative t m x)
      (‖t‖ / x ^ 2)

/-- Exact negative density represented by the right reciprocal-gap derivative. -/
theorem Complex.logarithmicPhaseRightReciprocalGapDerivative_eq_neg_density
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.logarithmicPhaseRightReciprocalGapDerivative t m x =
      -((‖t‖ / x ^ 2) /
        ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ ^ 2) := by
  unfold Complex.logarithmicPhaseRightReciprocalGapDerivative
  exact
    Real.neg_inv_sq_mul_eq_neg_div_norm_sq
      (Complex.logarithmicPhaseFourierTwistedDerivative t m x)
      (‖t‖ / x ^ 2)

/-- The left reciprocal-gap derivative is exactly the norm of the complex
coefficient derivative. -/
theorem Complex.logarithmicPhaseLeftReciprocalGapDerivative_eq_coefficientDerivativeNorm
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x =
      ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative
        t m x‖ := by
  exact
    (Complex.logarithmicPhaseLeftReciprocalGapDerivative_eq_density
      t m x).trans
      (Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative
        t m x).symm

/-- The negative right reciprocal-gap derivative is exactly the norm of the
complex coefficient derivative. -/
theorem Complex.neg_logarithmicPhaseRightReciprocalGapDerivative_eq_coefficientDerivativeNorm
    (t : ℝ) (m : ℤ) (x : ℝ) :
    -Complex.logarithmicPhaseRightReciprocalGapDerivative t m x =
      ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative
        t m x‖ := by
  have hnegativeDensity :=
    congrArg Neg.neg
      (Complex.logarithmicPhaseRightReciprocalGapDerivative_eq_neg_density
        t m x)
  have hdoubleNegative :
      -(-((‖t‖ / x ^ 2) /
          ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ ^ 2)) =
        (‖t‖ / x ^ 2) /
          ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ ^ 2 :=
    neg_neg _
  have hdensity :
      -Complex.logarithmicPhaseRightReciprocalGapDerivative t m x =
        (‖t‖ / x ^ 2) /
          ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ ^ 2 :=
    hnegativeDensity.trans hdoubleNegative
  exact
    hdensity.trans
      (Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative
        t m x).symm

/-- Absolute left reciprocal-gap variation equals the complex derivative norm. -/
theorem Complex.abs_logarithmicPhaseLeftReciprocalGapDerivative_eq_coefficientDerivativeNorm
    (t : ℝ) (m : ℤ) (x : ℝ) :
    |Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x| =
      ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative
        t m x‖ := by
  exact
    (Complex.abs_logarithmicPhaseLeftReciprocalGapDerivative t m x).trans
      (Complex.logarithmicPhaseLeftReciprocalGapDerivative_eq_coefficientDerivativeNorm
        t m x)

/-- Absolute right reciprocal-gap variation equals the complex derivative norm. -/
theorem Complex.abs_logarithmicPhaseRightReciprocalGapDerivative_eq_coefficientDerivativeNorm
    (t : ℝ) (m : ℤ) (x : ℝ) :
    |Complex.logarithmicPhaseRightReciprocalGapDerivative t m x| =
      ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative
        t m x‖ := by
  exact
    (Complex.abs_logarithmicPhaseRightReciprocalGapDerivative t m x).trans
      (Complex.neg_logarithmicPhaseRightReciprocalGapDerivative_eq_coefficientDerivativeNorm
        t m x)

/-- Integrability of the left scalar reciprocal-gap derivative follows from
the already constructed complex coefficient derivative. -/
theorem Complex.intervalIntegrable_logarithmicPhaseLeftReciprocalGapDerivative
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (m : ℤ) (left right : ℝ)
    (hleft : 0 < left) (hleft_right : left ≤ right)
    (hstationary :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m) :
    IntervalIntegrable
      (Complex.logarithmicPhaseLeftReciprocalGapDerivative t m)
      volume left right := by
  have hcomplex :=
    Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationary
  have hnorm :
      IntervalIntegrable
        (fun x : ℝ =>
          ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative
            t m x‖)
        volume left right :=
    hcomplex.norm
  have heq :
      Set.EqOn
        (Complex.logarithmicPhaseLeftReciprocalGapDerivative t m)
        (fun x : ℝ =>
          ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative
            t m x‖)
        [[left, right]] := by
    intro x _
    exact
      Complex.logarithmicPhaseLeftReciprocalGapDerivative_eq_coefficientDerivativeNorm
        t m x
  have hae :
      (fun x : ℝ =>
        ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative
          t m x‖) =ᵐ[volume.restrict (Ι left right)]
        Complex.logarithmicPhaseLeftReciprocalGapDerivative t m :=
    (ae_restrict_mem measurableSet_uIoc).mono
      (fun x hx =>
        (heq (Set.uIoc_subset_uIcc hx)).symm)
  exact IntervalIntegrable.congr hnorm hae

/-- Integrability of the right scalar reciprocal-gap derivative. -/
theorem Complex.intervalIntegrable_logarithmicPhaseRightReciprocalGapDerivative
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (m : ℤ) (left right : ℝ)
    (hleft : 0 < left) (hleft_right : left ≤ right)
    (hstationary :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m) :
    IntervalIntegrable
      (Complex.logarithmicPhaseRightReciprocalGapDerivative t m)
      volume left right := by
  have hleftDerivative :=
    Complex.intervalIntegrable_logarithmicPhaseLeftReciprocalGapDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationary
  have hnegLeft :
      IntervalIntegrable
        (fun x : ℝ =>
          -Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x)
        volume left right :=
    hleftDerivative.neg
  have heq :
      Set.EqOn
        (Complex.logarithmicPhaseRightReciprocalGapDerivative t m)
        (fun x : ℝ =>
          -Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x)
        [[left, right]] := by
    intro x _
    have hleftDensity :=
      Complex.logarithmicPhaseLeftReciprocalGapDerivative_eq_density t m x
    have hrightDensity :=
      Complex.logarithmicPhaseRightReciprocalGapDerivative_eq_neg_density
        t m x
    exact hrightDensity.trans (congrArg Neg.neg hleftDensity.symm)
  have hae :
      (fun x : ℝ =>
        -Complex.logarithmicPhaseLeftReciprocalGapDerivative t m x) =ᵐ[
          volume.restrict (Ι left right)]
        Complex.logarithmicPhaseRightReciprocalGapDerivative t m :=
    (ae_restrict_mem measurableSet_uIoc).mono
      (fun x hx =>
        (heq (Set.uIoc_subset_uIcc hx)).symm)
  exact IntervalIntegrable.congr hnegLeft hae

end

end LFunctions
end Boundary
