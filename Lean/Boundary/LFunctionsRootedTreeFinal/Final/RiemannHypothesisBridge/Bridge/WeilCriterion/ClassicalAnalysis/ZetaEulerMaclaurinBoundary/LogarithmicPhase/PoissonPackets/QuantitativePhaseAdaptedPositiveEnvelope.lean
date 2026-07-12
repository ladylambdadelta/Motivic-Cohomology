import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedTailArithmetic

/-!
# Positive-mode inverse-square envelope

The cubic and quartic terms of the closed packet majorant are absorbed into a
single inverse-square envelope because every positive angular gap is at least
one.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhasePositiveModeInverseSquareCoefficient_nonneg
    (t : ℝ) (a b : ℤ) (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a) :
    0 ≤ Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b := by
  unfold Complex.logarithmicPhasePositiveModeInverseSquareCoefficient
  have hlength := Complex.logarithmicPhaseQuantitativeSupportLength_nonneg a b hab
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg t _ hleft
  have hthird :=
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper_nonneg t _ hleft
  have hfirst : 0 ≤ (48 : ℝ) := by exact OfNat.zero_le 48
  have hsecond : 0 ≤ 6 *
      Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg (by exact OfNat.zero_le 6) hcurvature
  have hthirdTerm : 0 ≤
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg hlength hthird
  have hfourth : 0 ≤
      3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 :=
    mul_nonneg
      (mul_nonneg (by exact OfNat.zero_le 3) hlength)
      (sq_nonneg _)
  exact add_nonneg (add_nonneg (add_nonneg hfirst hsecond) hthirdTerm) hfourth

theorem Complex.logarithmicPhasePositiveModeClosedMajorant_le_termwiseSquare
    (t : ℝ) (a b m : ℤ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hm : 0 < m) :
    Complex.logarithmicPhasePositiveModeClosedMajorant t a b m ≤
      48 / (Complex.logarithmicPhasePositiveModeGap m) ^ 2 +
      (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) /
          (Complex.logarithmicPhasePositiveModeGap m) ^ 2 +
      (Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) /
          (Complex.logarithmicPhasePositiveModeGap m) ^ 2 +
      (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
          (Complex.logarithmicPhasePositiveModeGap m) ^ 2 := by
  unfold Complex.logarithmicPhasePositiveModeClosedMajorant
  unfold Complex.logarithmicPhaseAdaptedClosedMajorant
  have hgap := Complex.one_le_positiveModeGap m hm
  have hlength := Complex.logarithmicPhaseQuantitativeSupportLength_nonneg a b hab
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg t _ hleft
  have hthird :=
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper_nonneg t _ hleft
  have hsecondNumerator : 0 ≤ 6 *
      Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg (by exact OfNat.zero_le 6) hcurvature
  have hthirdNumerator : 0 ≤
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg hlength hthird
  have hfourthNumerator : 0 ≤
      3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 :=
    mul_nonneg
      (mul_nonneg (by exact OfNat.zero_le 3) hlength)
      (sq_nonneg _)
  have hsecond := Real.div_pow_three_le_div_pow_two_of_one_le
    hsecondNumerator hgap
  have hthirdBound := Real.div_pow_three_le_div_pow_two_of_one_le
    hthirdNumerator hgap
  have hfourth := Real.div_pow_four_le_div_pow_two_of_one_le
    hfourthNumerator hgap
  exact add_le_add
    (add_le_add (add_le_add (le_refl _) hsecond) hthirdBound) hfourth

theorem Complex.logarithmicPhasePositiveModeTermwiseSquare_eq_envelope
    (t : ℝ) (a b m : ℤ) :
    48 / (Complex.logarithmicPhasePositiveModeGap m) ^ 2 +
      (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) /
          (Complex.logarithmicPhasePositiveModeGap m) ^ 2 +
      (Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) /
          (Complex.logarithmicPhasePositiveModeGap m) ^ 2 +
      (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
          (Complex.logarithmicPhasePositiveModeGap m) ^ 2 =
      Complex.logarithmicPhasePositiveModeInverseSquareEnvelope t a b m := by
  unfold Complex.logarithmicPhasePositiveModeInverseSquareEnvelope
  unfold Complex.logarithmicPhasePositiveModeInverseSquareCoefficient
  let denominator := (Complex.logarithmicPhasePositiveModeGap m) ^ 2
  have hfirst := (add_div 48
    (6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) denominator).symm
  have hsecond := (add_div
    (48 + 6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a))
    (Complex.logarithmicPhaseQuantitativeSupportLength a b *
      Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) denominator).symm
  have hthird := (add_div
    (48 + 6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) +
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a))
    (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
      (Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) denominator).symm
  exact Eq.trans
    (congrArg (fun value : ℝ => value +
      (Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / denominator +
      (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
          denominator) hfirst)
    (Eq.trans
      (congrArg (fun value : ℝ => value +
        (3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
          (Complex.logarithmicPhaseAdaptedCurvatureUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) /
            denominator) hsecond)
      hthird)

theorem Complex.logarithmicPhasePositiveModeClosedMajorant_le_envelope
    (t : ℝ) (a b m : ℤ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hm : 0 < m) :
    Complex.logarithmicPhasePositiveModeClosedMajorant t a b m ≤
      Complex.logarithmicPhasePositiveModeInverseSquareEnvelope t a b m := by
  exact le_trans
    (Complex.logarithmicPhasePositiveModeClosedMajorant_le_termwiseSquare
      t a b m hab hleft hm)
    (le_of_eq
      (Complex.logarithmicPhasePositiveModeTermwiseSquare_eq_envelope
        t a b m))

end
end LFunctions
end Boundary
