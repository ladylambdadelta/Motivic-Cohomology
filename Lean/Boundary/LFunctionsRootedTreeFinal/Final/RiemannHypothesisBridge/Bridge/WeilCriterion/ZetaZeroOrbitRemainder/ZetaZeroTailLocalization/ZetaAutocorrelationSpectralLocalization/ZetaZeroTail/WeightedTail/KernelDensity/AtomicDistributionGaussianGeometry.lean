import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGeometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaCenteredZeroVerticalStrip.Owner

/-!
# Completed-zero Gaussian geometry

The completed-zero strip bounds every real spectral displacement by one.  The
real part of its square is therefore controlled entirely by the corresponding
imaginary displacement away from a fixed ordinate window.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The absolute real displacement between two completed zeros is at most one. -/
theorem completedZero_realDisplacement_abs_le_one
    (left right : ZetaCompletedZeroCoordinate) :
    |(left : ℂ).re - (right : ℂ).re| ≤ 1 := by
  have hleftStrip := zetaCompletedZero_re_mem_centeredCriticalStrip left
  have hrightStrip := zetaCompletedZero_re_mem_centeredCriticalStrip right
  have hleftAbsolute : |(left : ℂ).re| ≤ (1 / 2 : ℝ) :=
    abs_le.mpr hleftStrip
  have hrightAbsolute : |(right : ℂ).re| ≤ (1 / 2 : ℝ) :=
    abs_le.mpr hrightStrip
  have htriangle :
      |(left : ℂ).re - (right : ℂ).re| ≤
        |(left : ℂ).re| + |(right : ℂ).re| :=
    abs_sub (left : ℂ).re (right : ℂ).re
  have hsum :
      |(left : ℂ).re| + |(right : ℂ).re| ≤
        (1 / 2 : ℝ) + (1 / 2 : ℝ) :=
    add_le_add hleftAbsolute hrightAbsolute
  have hhalves : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 :=
    add_halves 1
  have hsumTransport :
      (|(left : ℂ).re| + |(right : ℂ).re| ≤
          (1 / 2 : ℝ) + (1 / 2 : ℝ)) =
        (|(left : ℂ).re| + |(right : ℂ).re| ≤ 1) :=
    congrArg
      (fun bound : ℝ =>
        |(left : ℂ).re| + |(right : ℂ).re| ≤ bound)
      hhalves
  exact le_trans htriangle
    (Eq.mp hsumTransport hsum)

/-- The real part of a squared completed-zero displacement is the difference
of the squared real and imaginary displacements. -/
theorem completedZero_displacement_square_re
    (left right : ZetaCompletedZeroCoordinate) :
    (((left : ℂ) - (right : ℂ)) ^ 2).re =
      ((left : ℂ).re - (right : ℂ).re) ^ 2 -
        ((left : ℂ).im - (right : ℂ).im) ^ 2 := by
  have hreal :
      ((left : ℂ) - (right : ℂ)).re =
        (left : ℂ).re - (right : ℂ).re :=
    Complex.sub_re (left : ℂ) (right : ℂ)
  have himaginary :
      ((left : ℂ) - (right : ℂ)).im =
        (left : ℂ).im - (right : ℂ).im :=
    Complex.sub_im (left : ℂ) (right : ℂ)
  calc
    (((left : ℂ) - (right : ℂ)) ^ 2).re =
        (((left : ℂ) - (right : ℂ)) *
          ((left : ℂ) - (right : ℂ))).re :=
      congrArg Complex.re (pow_two ((left : ℂ) - (right : ℂ)))
    _ =
        ((left : ℂ) - (right : ℂ)).re *
            ((left : ℂ) - (right : ℂ)).re -
          ((left : ℂ) - (right : ℂ)).im *
            ((left : ℂ) - (right : ℂ)).im :=
      Complex.mul_re
        ((left : ℂ) - (right : ℂ))
        ((left : ℂ) - (right : ℂ))
    _ =
        ((left : ℂ).re - (right : ℂ).re) *
            ((left : ℂ).re - (right : ℂ).re) -
          ((left : ℂ).im - (right : ℂ).im) *
            ((left : ℂ).im - (right : ℂ).im) :=
      congrArg₂
        (fun realPart imaginaryPart : ℝ =>
          realPart * realPart - imaginaryPart * imaginaryPart)
        hreal
        himaginary
    _ =
        ((left : ℂ).re - (right : ℂ).re) ^ 2 -
          ((left : ℂ).im - (right : ℂ).im) ^ 2 :=
      congrArg₂ Sub.sub
        (pow_two ((left : ℂ).re - (right : ℂ).re)).symm
        (pow_two ((left : ℂ).im - (right : ℂ).im)).symm

/-- The fixed positive quadratic margin left after discarding the ordinate
window of radius two. -/
def completedZeroGaussianSeparationMargin : ℝ :=
  (2 : ℝ) ^ 2 - (1 : ℝ) ^ 2

/-- The fixed quadratic separation margin is positive. -/
theorem completedZeroGaussianSeparationMargin_pos :
    0 < completedZeroGaussianSeparationMargin := by
  have habsoluteOne : |(1 : ℝ)| = 1 :=
    abs_of_nonneg zero_le_one
  have habsoluteTwo : |(2 : ℝ)| = 2 :=
    abs_of_nonneg zero_le_two
  have habsoluteStrict : |(1 : ℝ)| < |(2 : ℝ)| :=
    Eq.subst
      (motive := fun right : ℝ => |(1 : ℝ)| < right)
      habsoluteTwo.symm
      (Eq.subst
        (motive := fun left : ℝ => left < 2)
        habsoluteOne.symm
        one_lt_two)
  have hsquareStrict : (1 : ℝ) ^ 2 < (2 : ℝ) ^ 2 :=
    sq_lt_sq.mpr habsoluteStrict
  exact sub_pos.mpr hsquareStrict

/-- Outside the radius-two ordinate window, the squared completed-zero
displacement has uniformly negative real part. -/
theorem completedZero_displacement_square_re_le_negativeMargin
    (left right : ZetaCompletedZeroCoordinate)
    (himaginary :
      2 ≤ |(left : ℂ).im - (right : ℂ).im|) :
    (((left : ℂ) - (right : ℂ)) ^ 2).re ≤
      -completedZeroGaussianSeparationMargin := by
  have habsoluteOne : |(1 : ℝ)| = 1 :=
    abs_of_nonneg zero_le_one
  have habsoluteTwo : |(2 : ℝ)| = 2 :=
    abs_of_nonneg zero_le_two
  have hrealAbsolute :
      |(left : ℂ).re - (right : ℂ).re| ≤ |(1 : ℝ)| :=
    Eq.subst
      (motive := fun value : ℝ =>
        |(left : ℂ).re - (right : ℂ).re| ≤ value)
      habsoluteOne.symm
      (completedZero_realDisplacement_abs_le_one left right)
  have himaginaryAbsolute :
      |(2 : ℝ)| ≤ |(left : ℂ).im - (right : ℂ).im| :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ |(left : ℂ).im - (right : ℂ).im|)
      habsoluteTwo.symm
      himaginary
  have hrealSquare :
      ((left : ℂ).re - (right : ℂ).re) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    sq_le_sq.mpr hrealAbsolute
  have himaginarySquare :
      (2 : ℝ) ^ 2 ≤
        ((left : ℂ).im - (right : ℂ).im) ^ 2 :=
    sq_le_sq.mpr himaginaryAbsolute
  have hdifference :
      ((left : ℂ).re - (right : ℂ).re) ^ 2 -
          ((left : ℂ).im - (right : ℂ).im) ^ 2 ≤
        (1 : ℝ) ^ 2 - (2 : ℝ) ^ 2 :=
    sub_le_sub hrealSquare himaginarySquare
  have hnegativeMargin :
      (1 : ℝ) ^ 2 - (2 : ℝ) ^ 2 =
        -completedZeroGaussianSeparationMargin :=
    (neg_sub ((2 : ℝ) ^ 2) ((1 : ℝ) ^ 2)).symm
  calc
    (((left : ℂ) - (right : ℂ)) ^ 2).re =
        ((left : ℂ).re - (right : ℂ).re) ^ 2 -
          ((left : ℂ).im - (right : ℂ).im) ^ 2 :=
      completedZero_displacement_square_re left right
    _ ≤ (1 : ℝ) ^ 2 - (2 : ℝ) ^ 2 := hdifference
    _ = -completedZeroGaussianSeparationMargin := hnegativeMargin

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
