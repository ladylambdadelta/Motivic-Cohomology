import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianKernel
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.PolynomialMultiplierGrowth
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianRealDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianNaturalScaleLimits
namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
def completedZeroScaledGaussianNorm
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) : ℝ :=
  ‖fullGaussianLaplaceKernel
    ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖

def completedZeroScaledGaussianEnvelope
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) : ℝ :=
  (fullGaussianLaplaceKernelNormalizationNorm *
      Real.exp (scale ^ 2 / 4)) *
    Real.exp
      (-(scale ^ 2 / 4) *
        ((rho : ℂ).im - (target : ℂ).im) ^ 2)

def completedZeroGaussianQuadratic
    (target rho : ZetaCompletedZeroCoordinate) : ℝ :=
  ((rho : ℂ).re - (target : ℂ).re) ^ 2 -
    ((rho : ℂ).im - (target : ℂ).im) ^ 2

def completedZeroScaledGaussianCoordinateNorm
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) : ℝ :=
  fullGaussianLaplaceKernelNormalizationNorm *
    Real.exp
      ((scale ^ 2 / 4) *
        completedZeroGaussianQuadratic target rho)

def completedZeroNaturalScaleGaussian
    (target rho : ZetaCompletedZeroCoordinate)
    (n : ℕ) : ℂ :=
  fullGaussianLaplaceKernel
    (((n : ℝ) + 1 : ℂ) * ((rho : ℂ) - (target : ℂ)))

def completedZeroNaturalScaleGaussianCoordinateNorm
    (target rho : ZetaCompletedZeroCoordinate)
    (n : ℕ) : ℝ :=
  completedZeroScaledGaussianCoordinateNorm
    target rho ((n : ℝ) + 1)

theorem completedZero_scaledDisplacement_square_div_four_re
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) :
    ((((scale : ℂ) * ((rho : ℂ) - (target : ℂ))) ^ 2 / 4).re) =
      (scale ^ 2 / 4) *
        (((rho : ℂ).re - (target : ℂ).re) ^ 2 -
          ((rho : ℂ).im - (target : ℂ).im) ^ 2) := by
  let displacement : ℂ := (rho : ℂ) - (target : ℂ)
  have hscalePower :
      (scale : ℂ) ^ 2 = ((scale ^ 2 : ℝ) : ℂ) :=
    (Complex.ofReal_pow scale 2).symm
  have hproductPower :
      ((scale : ℂ) * displacement) ^ 2 =
        (scale : ℂ) ^ 2 * displacement ^ 2 :=
    mul_pow (scale : ℂ) displacement 2
  have hdivideReassociate :
      ((scale : ℂ) ^ 2 * displacement ^ 2) / 4 =
        ((scale : ℂ) ^ 2 / 4) * displacement ^ 2 :=
    mul_div_right_comm
      ((scale : ℂ) ^ 2)
      (displacement ^ 2)
      4
  have hscaleDivision :
      (scale : ℂ) ^ 2 / 4 = ((scale ^ 2 / 4 : ℝ) : ℂ) := by
    have hcastDivision :
        ((scale ^ 2 / 4 : ℝ) : ℂ) =
          ((scale ^ 2 : ℝ) : ℂ) / ((4 : ℝ) : ℂ) :=
      Complex.ofReal_div (scale ^ 2) 4
    have hfourCast : ((4 : ℝ) : ℂ) = (4 : ℂ) :=
      Eq.refl (4 : ℂ)
    exact Eq.trans
      (congrArg (fun numerator : ℂ => numerator / (4 : ℂ)) hscalePower)
      (Eq.trans
        (congrArg
          (fun denominator : ℂ =>
            ((scale ^ 2 : ℝ) : ℂ) / denominator)
          hfourCast.symm)
        hcastDivision.symm)
  have hcomplexIdentity :
      (((scale : ℂ) * displacement) ^ 2 / 4) =
        ((scale ^ 2 / 4 : ℝ) : ℂ) * displacement ^ 2 :=
    Eq.trans
      (congrArg (fun value : ℂ => value / 4) hproductPower)
      (Eq.trans hdivideReassociate
        (congrArg
          (fun value : ℂ => value * displacement ^ 2)
          hscaleDivision))
  have hrealScalarProduct :
      (((scale ^ 2 / 4 : ℝ) : ℂ) * displacement ^ 2).re =
        (scale ^ 2 / 4) * (displacement ^ 2).re := by
    have hmulReal :=
      Complex.mul_re
        (((scale ^ 2 / 4 : ℝ) : ℂ))
        (displacement ^ 2)
    have hscalarReal : (((scale ^ 2 / 4 : ℝ) : ℂ)).re =
        scale ^ 2 / 4 :=
      Complex.ofReal_re (scale ^ 2 / 4)
    have hscalarImaginary : (((scale ^ 2 / 4 : ℝ) : ℂ)).im = 0 :=
      Complex.ofReal_im (scale ^ 2 / 4)
    exact Eq.trans hmulReal
      (Eq.trans
        (congrArg₂ Sub.sub
          (congrArg
            (fun value : ℝ => value * (displacement ^ 2).re)
            hscalarReal)
          (congrArg
            (fun value : ℝ => value * (displacement ^ 2).im)
            hscalarImaginary))
        (Eq.trans
          (congrArg
            (fun value : ℝ =>
              (scale ^ 2 / 4) * (displacement ^ 2).re - value)
            (zero_mul (displacement ^ 2).im))
          (sub_zero
            ((scale ^ 2 / 4) * (displacement ^ 2).re))))
  have hdisplacementReal :
      (displacement ^ 2).re =
        ((rho : ℂ).re - (target : ℂ).re) ^ 2 -
          ((rho : ℂ).im - (target : ℂ).im) ^ 2 :=
    completedZero_displacement_square_re rho target
  exact Eq.trans
    (congrArg Complex.re hcomplexIdentity)
    (Eq.trans hrealScalarProduct
      (congrArg
        (fun value : ℝ => (scale ^ 2 / 4) * value)
        hdisplacementReal))

theorem completedZero_scaledDisplacement_square_div_four_re_le
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) :
    ((((scale : ℂ) * ((rho : ℂ) - (target : ℂ))) ^ 2 / 4).re) ≤
      scale ^ 2 / 4 -
        (scale ^ 2 / 4) *
          ((rho : ℂ).im - (target : ℂ).im) ^ 2 := by
  let realDisplacement : ℝ :=
    (rho : ℂ).re - (target : ℂ).re
  let imaginaryDisplacement : ℝ :=
    (rho : ℂ).im - (target : ℂ).im
  let scaleFactor : ℝ := scale ^ 2 / 4
  have hrealAbsolute : |realDisplacement| ≤ |(1 : ℝ)| := by
    have habsoluteOne : |(1 : ℝ)| = 1 :=
      abs_of_nonneg zero_le_one
    exact Eq.subst
      (motive := fun value : ℝ => |realDisplacement| ≤ value)
      habsoluteOne.symm
      (completedZero_realDisplacement_abs_le_one rho target)
  have hrealSquare : realDisplacement ^ 2 ≤ (1 : ℝ) ^ 2 :=
    sq_le_sq.mpr hrealAbsolute
  have honeSquare : (1 : ℝ) ^ 2 = 1 :=
    Eq.trans (pow_two (1 : ℝ)) (one_mul 1)
  have hrealSquareOne : realDisplacement ^ 2 ≤ 1 :=
    hrealSquare.trans_eq honeSquare
  have hscaleSquareNonnegative : 0 ≤ scale ^ 2 :=
    sq_nonneg scale
  have hfourPositive : (0 : ℝ) < 4 :=
    zero_lt_four
  have hscaleFactorNonnegative : 0 ≤ scaleFactor :=
    div_nonneg hscaleSquareNonnegative (le_of_lt hfourPositive)
  have hscaledRealSquare :
      scaleFactor * realDisplacement ^ 2 ≤ scaleFactor * 1 :=
    mul_le_mul_of_nonneg_left hrealSquareOne hscaleFactorNonnegative
  have hsubtractImaginary :
      scaleFactor * realDisplacement ^ 2 -
          scaleFactor * imaginaryDisplacement ^ 2 ≤
        scaleFactor * 1 - scaleFactor * imaginaryDisplacement ^ 2 :=
    sub_le_sub_right hscaledRealSquare
      (scaleFactor * imaginaryDisplacement ^ 2)
  have hleftDistribute :
      scaleFactor *
          (realDisplacement ^ 2 - imaginaryDisplacement ^ 2) =
        scaleFactor * realDisplacement ^ 2 -
          scaleFactor * imaginaryDisplacement ^ 2 :=
    mul_sub scaleFactor
      (realDisplacement ^ 2)
      (imaginaryDisplacement ^ 2)
  have hrightOne :
      scaleFactor * 1 - scaleFactor * imaginaryDisplacement ^ 2 =
        scaleFactor - scaleFactor * imaginaryDisplacement ^ 2 :=
    congrArg
      (fun value : ℝ => value - scaleFactor * imaginaryDisplacement ^ 2)
      (mul_one scaleFactor)
  have halgebraicBound :
      scaleFactor *
          (realDisplacement ^ 2 - imaginaryDisplacement ^ 2) ≤
        scaleFactor - scaleFactor * imaginaryDisplacement ^ 2 :=
    hleftDistribute.trans_le (hsubtractImaginary.trans_eq hrightOne)
  calc
    ((((scale : ℂ) * ((rho : ℂ) - (target : ℂ))) ^ 2 / 4).re) =
        scaleFactor *
          (realDisplacement ^ 2 - imaginaryDisplacement ^ 2) :=
      completedZero_scaledDisplacement_square_div_four_re target rho scale
    _ ≤ scaleFactor - scaleFactor * imaginaryDisplacement ^ 2 :=
      halgebraicBound

theorem realGaussianExponent_eq_product
    (scale displacement : ℝ) :
    Real.exp
        (scale ^ 2 / 4 -
          (scale ^ 2 / 4) * displacement ^ 2) =
      Real.exp (scale ^ 2 / 4) *
        Real.exp (-(scale ^ 2 / 4) * displacement ^ 2) := by
  have hnegativeProduct :
      -((scale ^ 2 / 4) * displacement ^ 2) =
        -(scale ^ 2 / 4) * displacement ^ 2 :=
    (neg_mul (scale ^ 2 / 4) (displacement ^ 2)).symm
  have hsubAsAdd :
      scale ^ 2 / 4 -
          (scale ^ 2 / 4) * displacement ^ 2 =
        scale ^ 2 / 4 +
          (-(scale ^ 2 / 4) * displacement ^ 2) :=
    Eq.trans
      (sub_eq_add_neg
        (scale ^ 2 / 4)
        ((scale ^ 2 / 4) * displacement ^ 2))
      (congrArg
        (fun value : ℝ => scale ^ 2 / 4 + value)
        hnegativeProduct)
  exact Eq.trans
    (congrArg Real.exp hsubAsAdd)
    (Real.exp_add
      (scale ^ 2 / 4)
      (-(scale ^ 2 / 4) * displacement ^ 2))

theorem fullGaussianLaplaceKernel_scaled_shift_norm_le_realGaussian
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) :
    completedZeroScaledGaussianNorm target rho scale ≤
      completedZeroScaledGaussianEnvelope target rho scale := by
  let displacement : ℂ :=
    (scale : ℂ) * ((rho : ℂ) - (target : ℂ))
  let imaginaryDisplacement : ℝ :=
    (rho : ℂ).im - (target : ℂ).im
  have hnormFormula :
      ‖fullGaussianLaplaceKernel displacement‖ =
        fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp ((displacement ^ 2 / 4).re) :=
    norm_fullGaussianLaplaceKernel_eq_exp_re displacement
  have hexponentBound :
      (displacement ^ 2 / 4).re ≤
        scale ^ 2 / 4 -
          (scale ^ 2 / 4) *
            ((rho : ℂ).im - (target : ℂ).im) ^ 2 :=
    completedZero_scaledDisplacement_square_div_four_re_le
      target rho scale
  have hexponentialBound :
      Real.exp ((displacement ^ 2 / 4).re) ≤
        Real.exp
          (scale ^ 2 / 4 -
            (scale ^ 2 / 4) *
              ((rho : ℂ).im - (target : ℂ).im) ^ 2) :=
    Real.exp_le_exp.mpr hexponentBound
  have hbaseNormNonnegative :
      0 ≤ fullGaussianLaplaceKernelNormalizationNorm :=
    norm_nonneg (((Real.pi : ℂ) / (1 : ℂ)) ^ (1 / 2 : ℂ))
  have hscaledExponentialBound :
      fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp ((displacement ^ 2 / 4).re) ≤
        fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp
            (scale ^ 2 / 4 -
              (scale ^ 2 / 4) *
                ((rho : ℂ).im - (target : ℂ).im) ^ 2) :=
    mul_le_mul_of_nonneg_left hexponentialBound hbaseNormNonnegative
  have hexponentialProduct :
      Real.exp
          (scale ^ 2 / 4 -
            (scale ^ 2 / 4) *
              ((rho : ℂ).im - (target : ℂ).im) ^ 2) =
        Real.exp (scale ^ 2 / 4) *
          Real.exp
            (-(scale ^ 2 / 4) *
              ((rho : ℂ).im - (target : ℂ).im) ^ 2) :=
    realGaussianExponent_eq_product scale imaginaryDisplacement
  have hreassociate :
      fullGaussianLaplaceKernelNormalizationNorm *
          (Real.exp (scale ^ 2 / 4) *
            Real.exp
              (-(scale ^ 2 / 4) *
                ((rho : ℂ).im - (target : ℂ).im) ^ 2)) =
        (fullGaussianLaplaceKernelNormalizationNorm *
            Real.exp (scale ^ 2 / 4)) *
          Real.exp
            (-(scale ^ 2 / 4) *
              ((rho : ℂ).im - (target : ℂ).im) ^ 2) :=
    (mul_assoc
      fullGaussianLaplaceKernelNormalizationNorm
      (Real.exp (scale ^ 2 / 4))
      (Real.exp
        (-(scale ^ 2 / 4) *
          ((rho : ℂ).im - (target : ℂ).im) ^ 2))).symm
  have hrawIdentity :
      ‖fullGaussianLaplaceKernel displacement‖ =
        fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp ((displacement ^ 2 / 4).re) :=
    hnormFormula
  have hrawExponentialBound :
      fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp ((displacement ^ 2 / 4).re) ≤
        fullGaussianLaplaceKernelNormalizationNorm *
        Real.exp
          (scale ^ 2 / 4 -
            (scale ^ 2 / 4) * imaginaryDisplacement ^ 2) :=
    hscaledExponentialBound
  have hrawProductIdentity :
      fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp
            (scale ^ 2 / 4 -
              (scale ^ 2 / 4) * imaginaryDisplacement ^ 2) =
        (fullGaussianLaplaceKernelNormalizationNorm *
            Real.exp (scale ^ 2 / 4)) *
          Real.exp
            (-(scale ^ 2 / 4) * imaginaryDisplacement ^ 2) :=
    Eq.trans
      (congrArg
        (fun value : ℝ =>
          fullGaussianLaplaceKernelNormalizationNorm * value)
        hexponentialProduct)
      hreassociate
  have hrawBound :
      ‖fullGaussianLaplaceKernel displacement‖ ≤
        (fullGaussianLaplaceKernelNormalizationNorm *
            Real.exp (scale ^ 2 / 4)) *
          Real.exp
            (-(scale ^ 2 / 4) * imaginaryDisplacement ^ 2) :=
    hrawIdentity.trans_le
      (hrawExponentialBound.trans_eq hrawProductIdentity)
  have hleftDefinition :
      completedZeroScaledGaussianNorm target rho scale =
        ‖fullGaussianLaplaceKernel displacement‖ :=
    rfl
  have hrightDefinition :
      (fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp (scale ^ 2 / 4)) *
        Real.exp
          (-(scale ^ 2 / 4) * imaginaryDisplacement ^ 2) =
        completedZeroScaledGaussianEnvelope target rho scale :=
    rfl
  exact hleftDefinition.trans_le
    (hrawBound.trans_eq hrightDefinition)

theorem fullGaussianLaplaceKernel_scaled_shift_norm_eq
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) :
    completedZeroScaledGaussianNorm target rho scale =
      completedZeroScaledGaussianCoordinateNorm target rho scale := by
  have hleftDefinition :
      completedZeroScaledGaussianNorm target rho scale =
        ‖fullGaussianLaplaceKernel
          ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ :=
    rfl
  have hrawIdentity :
      ‖fullGaussianLaplaceKernel
          ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ =
        fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp
            ((scale ^ 2 / 4) *
              completedZeroGaussianQuadratic target rho) :=
    Eq.trans
    (norm_fullGaussianLaplaceKernel_eq_exp_re
      ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))))
    (congrArg
      (fun value : ℝ =>
        fullGaussianLaplaceKernelNormalizationNorm * Real.exp value)
      (completedZero_scaledDisplacement_square_div_four_re
        target rho scale))
  have hrightDefinition :
      fullGaussianLaplaceKernelNormalizationNorm *
          Real.exp
            ((scale ^ 2 / 4) *
              completedZeroGaussianQuadratic target rho) =
        completedZeroScaledGaussianCoordinateNorm target rho scale :=
    rfl
  exact Eq.trans hleftDefinition
    (Eq.trans hrawIdentity hrightDefinition)

theorem completedZeroNaturalScaleGaussian_norm_eq_coordinateNorm
    (target rho : ZetaCompletedZeroCoordinate)
    (n : ℕ) :
    ‖completedZeroNaturalScaleGaussian target rho n‖ =
      completedZeroNaturalScaleGaussianCoordinateNorm target rho n := by
  have hleftDefinition :
      ‖completedZeroNaturalScaleGaussian target rho n‖ =
        completedZeroScaledGaussianNorm target rho ((n : ℝ) + 1) :=
    by
    have hscaleCast :
        ((n : ℝ) : ℂ) + (1 : ℂ) =
          ((((n : ℝ) + 1 : ℝ)) : ℂ) :=
      (Complex.ofReal_add (n : ℝ) 1).symm
    have hnaturalDefinition :
        completedZeroNaturalScaleGaussian target rho n =
          fullGaussianLaplaceKernel
            ((((n : ℝ) + 1 : ℝ) : ℂ) *
              ((rho : ℂ) - (target : ℂ))) :=
      Eq.trans
        (Eq.refl
          (fullGaussianLaplaceKernel
            ((((n : ℝ) : ℂ) + (1 : ℂ)) *
              ((rho : ℂ) - (target : ℂ)))))
        (congrArg fullGaussianLaplaceKernel
          (congrArg
            (fun value : ℂ =>
              value * ((rho : ℂ) - (target : ℂ)))
            hscaleCast))
    have hscaledDefinition :
        completedZeroScaledGaussianNorm target rho ((n : ℝ) + 1) =
          ‖fullGaussianLaplaceKernel
            ((((n : ℝ) + 1 : ℝ) : ℂ) *
              ((rho : ℂ) - (target : ℂ)))‖ :=
      rfl
    exact Eq.trans
      (congrArg Norm.norm hnaturalDefinition)
      hscaledDefinition.symm
  have hrightDefinition :
      completedZeroScaledGaussianCoordinateNorm target rho ((n : ℝ) + 1) =
        completedZeroNaturalScaleGaussianCoordinateNorm target rho n :=
    rfl
  exact Eq.trans hleftDefinition
    (Eq.trans
      (fullGaussianLaplaceKernel_scaled_shift_norm_eq
        target rho ((n : ℝ) + 1))
      hrightDefinition)

theorem real_le_mul_mul_of_le_of_le
    (value kernel gaussian decay height : ℝ)
    (hvalue : value ≤ kernel * gaussian)
    (hgaussian : gaussian ≤ decay * height)
    (hkernelNonnegative : 0 ≤ kernel) :
    value ≤ (kernel * decay) * height := by
  have hscaled :
      kernel * gaussian ≤ kernel * (decay * height) :=
    mul_le_mul_of_nonneg_left hgaussian hkernelNonnegative
  have hreassociate :
      kernel * (decay * height) = (kernel * decay) * height :=
    (mul_assoc kernel decay height).symm
  exact hvalue.trans (hscaled.trans_eq hreassociate)

theorem zetaCompletedZeroCenteredHeight_eq_one_add_abs_im
    (rho : ZetaCompletedZeroCoordinate) :
    zetaCompletedZeroCenteredHeight rho = 1 + |(rho : ℂ).im| :=
  Eq.trans
    (zetaCompletedZeroCenteredHeight_eq_one_add_norm_im rho)
    (congrArg
      (fun value : ℝ => 1 + value)
      (Real.norm_eq_abs (rho : ℂ).im))

/-- Radius-two ordinate separation makes the completed-zero Gaussian
quadratic strictly negative. -/
theorem completedZeroGaussianQuadratic_lt_zero
    (target rho : ZetaCompletedZeroCoordinate)
    (himaginary :
      2 ≤ |(rho : ℂ).im - (target : ℂ).im|) :
    completedZeroGaussianQuadratic target rho < 0 := by
  have hquadraticBound :
      completedZeroGaussianQuadratic target rho ≤
        -completedZeroGaussianSeparationMargin :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ -completedZeroGaussianSeparationMargin)
      (completedZero_displacement_square_re rho target)
      (completedZero_displacement_square_re_le_negativeMargin
        rho target himaginary)
  exact lt_of_le_of_lt hquadraticBound
    (neg_neg_of_pos completedZeroGaussianSeparationMargin_pos)

/-- A shifted positive-scale full Gaussian has arbitrary polynomial decay on
the completed-zero set. -/
theorem exists_fullGaussianLaplaceKernel_scaled_shift_decay
    (target : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (hscale : 0 < scale)
    (degree : ℕ) :
    ∃ bound : ℝ,
      0 < bound ∧
      ∀ rho : ZetaCompletedZeroCoordinate,
        ‖fullGaussianLaplaceKernel
          ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ ≤
            bound *
              zetaCompletedZeroCenteredHeight rho ^ (-(degree : ℤ)) := by
  have hscaleSquarePositive : 0 < scale ^ 2 :=
    sq_pos_of_pos hscale
  have hfourPositive : (0 : ℝ) < 4 :=
    zero_lt_four
  have hgaussianRatePositive : 0 < scale ^ 2 / 4 :=
    div_pos hscaleSquarePositive hfourPositive
  obtain ⟨decayBound, hdecayBoundPositive, hdecay⟩ :=
    exists_shiftedRealGaussian_centeredHeight_decay
      (scale ^ 2 / 4) (target : ℂ).im
      hgaussianRatePositive degree
  let kernelBound : ℝ :=
    fullGaussianLaplaceKernelNormalizationNorm *
      Real.exp (scale ^ 2 / 4)
  have hbaseNonzero :
      ((Real.pi : ℂ) / (1 : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro hzero
    have hcharacterization :=
      (Complex.cpow_eq_zero_iff
        ((Real.pi : ℂ) / (1 : ℂ))
        (1 / 2 : ℂ)).mp hzero
    have hbaseZero : ((Real.pi : ℂ) / (1 : ℂ)) = 0 :=
      hcharacterization.1
    exact
      (div_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        one_ne_zero)
      hbaseZero
  have hkernelBoundPositive : 0 < kernelBound :=
    mul_pos
      (norm_pos_iff.mpr hbaseNonzero)
      (Real.exp_pos (scale ^ 2 / 4))
  have hkernelDecay :
      ∀ rho : ZetaCompletedZeroCoordinate,
        ‖fullGaussianLaplaceKernel
            ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ ≤
          (kernelBound * decayBound) *
            zetaCompletedZeroCenteredHeight rho ^ (-(degree : ℤ)) := by
    intro rho
    have hkernelEstimate :
        ‖fullGaussianLaplaceKernel
            ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ ≤
          kernelBound *
            Real.exp
              (-(scale ^ 2 / 4) *
                ((rho : ℂ).im - (target : ℂ).im) ^ 2) :=
      fullGaussianLaplaceKernel_scaled_shift_norm_le_realGaussian
        target rho scale
    have hdecayEstimate :
        Real.exp
            (-(scale ^ 2 / 4) *
              ((rho : ℂ).im - (target : ℂ).im) ^ 2) ≤
          decayBound *
            (1 + |(rho : ℂ).im|) ^ (-(degree : ℤ)) :=
      hdecay (rho : ℂ).im
    have hheightIdentity :
        zetaCompletedZeroCenteredHeight rho =
          1 + |(rho : ℂ).im| :=
      zetaCompletedZeroCenteredHeight_eq_one_add_abs_im rho
    have hheightPower :
        (1 + |(rho : ℂ).im|) ^ (-(degree : ℤ)) =
          zetaCompletedZeroCenteredHeight rho ^ (-(degree : ℤ)) :=
      congrArg
        (fun value : ℝ => value ^ (-(degree : ℤ)))
        hheightIdentity.symm
    have hdecayCentered :
        Real.exp
            (-(scale ^ 2 / 4) *
              ((rho : ℂ).im - (target : ℂ).im) ^ 2) ≤
          decayBound *
            zetaCompletedZeroCenteredHeight rho ^ (-(degree : ℤ)) :=
      hdecayEstimate.trans_eq
        (congrArg
          (fun value : ℝ => decayBound * value)
          hheightPower)
    exact real_le_mul_mul_of_le_of_le
      ‖fullGaussianLaplaceKernel
        ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖
      kernelBound
      (Real.exp
        (-(scale ^ 2 / 4) *
          ((rho : ℂ).im - (target : ℂ).im) ^ 2))
      decayBound
      (zetaCompletedZeroCenteredHeight rho ^ (-(degree : ℤ)))
      hkernelEstimate
      hdecayCentered
      (le_of_lt hkernelBoundPositive)
  
  exact
    ⟨kernelBound * decayBound,
      mul_pos hkernelBoundPositive hdecayBoundPositive,
      hkernelDecay⟩

/-- At every ordinate separated from the target by at least two, natural
Gaussian scales converge pointwise to zero. -/
theorem fullGaussianLaplaceKernel_natScale_shift_tendsto_zero
    (target rho : ZetaCompletedZeroCoordinate)
    (himaginary :
      2 ≤ |(rho : ℂ).im - (target : ℂ).im|) :
    Filter.Tendsto
      (completedZeroNaturalScaleGaussian target rho)
      Filter.atTop
      (nhds 0) := by
  have hquadraticNegative :
      completedZeroGaussianQuadratic target rho < 0 :=
    completedZeroGaussianQuadratic_lt_zero target rho himaginary
  have hquadraticDivNegative :
      completedZeroGaussianQuadratic target rho / 4 < 0 :=
    div_neg_of_neg_of_pos hquadraticNegative zero_lt_four
  have hratePositive :
      0 < -(completedZeroGaussianQuadratic target rho / 4) :=
    neg_pos.mpr hquadraticDivNegative
  have hscaledExponentialLimit :
      Filter.Tendsto
        (fun n : ℕ =>
          fullGaussianLaplaceKernelNormalizationNorm *
            Real.exp
              ((((n : ℝ) + 1) ^ 2 / 4) *
                completedZeroGaussianQuadratic target rho))
        Filter.atTop
        (nhds 0) :=
    naturalScaleScaledGaussianExponential_tendsto_zero
      fullGaussianLaplaceKernelNormalizationNorm
      (completedZeroGaussianQuadratic target rho)
      (-(completedZeroGaussianQuadratic target rho / 4))
      (Eq.refl (-(completedZeroGaussianQuadratic target rho / 4)))
      hratePositive
  have hcoordinateNormLimit :
      Filter.Tendsto
        (completedZeroNaturalScaleGaussianCoordinateNorm target rho)
        Filter.atTop
        (nhds 0) :=
    hscaledExponentialLimit
  have hnormLimit :
      Filter.Tendsto
        (fun n : ℕ =>
          ‖completedZeroNaturalScaleGaussian target rho n‖)
        Filter.atTop
        (nhds 0) := by
    have hnormFunctionEquality :
        (fun n : ℕ =>
          ‖completedZeroNaturalScaleGaussian target rho n‖) =
          completedZeroNaturalScaleGaussianCoordinateNorm target rho := by
      funext n
      exact completedZeroNaturalScaleGaussian_norm_eq_coordinateNorm
        target rho n
    exact realSequence_tendsto_zero_of_eq
      (fun n : ℕ =>
        ‖completedZeroNaturalScaleGaussian target rho n‖)
      (completedZeroNaturalScaleGaussianCoordinateNorm target rho)
      hnormFunctionEquality
      hcoordinateNormLimit
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr hnormLimit

/-- Outside the radius-two ordinate window, every natural Gaussian scale is
norm-dominated by scale one. -/
theorem fullGaussianLaplaceKernel_natScale_shift_norm_le_oneScale
    (target rho : ZetaCompletedZeroCoordinate)
    (himaginary :
      2 ≤ |(rho : ℂ).im - (target : ℂ).im|)
    (n : ℕ) :
    ‖completedZeroNaturalScaleGaussian target rho n‖ ≤
      completedZeroScaledGaussianNorm target rho 1 := by
  let quadratic : ℝ :=
    ((rho : ℂ).re - (target : ℂ).re) ^ 2 -
      ((rho : ℂ).im - (target : ℂ).im) ^ 2
  have hquadraticBound :
      quadratic ≤ -completedZeroGaussianSeparationMargin :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ -completedZeroGaussianSeparationMargin)
      (completedZero_displacement_square_re rho target)
      (completedZero_displacement_square_re_le_negativeMargin
        rho target himaginary)
  have hquadraticNonpositive : quadratic ≤ 0 :=
    le_trans hquadraticBound
      (le_of_lt
        (neg_neg_of_pos completedZeroGaussianSeparationMargin_pos))
  have hscaleOne : 1 ≤ (n : ℝ) + 1 :=
    le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hscaleNonnegative : 0 ≤ (n : ℝ) + 1 :=
    le_trans zero_le_one hscaleOne
  have habsoluteOne : |(1 : ℝ)| = 1 :=
    abs_of_nonneg zero_le_one
  have habsoluteScale : |(n : ℝ) + 1| = (n : ℝ) + 1 :=
    abs_of_nonneg hscaleNonnegative
  have habsoluteScaleBound :
      |(1 : ℝ)| ≤ |(n : ℝ) + 1| :=
    Eq.mpr
      (congrArg₂ LE.le habsoluteOne habsoluteScale)
      hscaleOne
  have hscaleSquare : (1 : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 :=
    sq_le_sq.mpr habsoluteScaleBound
  have hscaledQuadratic :
      ((n : ℝ) + 1) ^ 2 * quadratic ≤ (1 : ℝ) ^ 2 * quadratic :=
    mul_le_mul_of_nonpos_right hscaleSquare hquadraticNonpositive
  have hdivideScaledQuadratic :
      (((n : ℝ) + 1) ^ 2 * quadratic) / 4 ≤
        ((1 : ℝ) ^ 2 * quadratic) / 4 :=
    div_le_div_of_nonneg_right hscaledQuadratic (le_of_lt zero_lt_four)
  have hleftExponent :
      (((n : ℝ) + 1) ^ 2 / 4) * quadratic =
        (((n : ℝ) + 1) ^ 2 * quadratic) / 4 :=
    div_mul_eq_mul_div
      (((n : ℝ) + 1) ^ 2)
      4
      quadratic
  have hrightExponent :
      ((1 : ℝ) ^ 2 / 4) * quadratic =
        ((1 : ℝ) ^ 2 * quadratic) / 4 :=
    div_mul_eq_mul_div ((1 : ℝ) ^ 2) 4 quadratic
  have hexponentBound :
      (((n : ℝ) + 1) ^ 2 / 4) * quadratic ≤
        ((1 : ℝ) ^ 2 / 4) * quadratic :=
    hleftExponent.trans_le
      (hdivideScaledQuadratic.trans_eq hrightExponent.symm)
  have hexponentialBound :=
    Real.exp_le_exp.mpr hexponentBound
  have hbaseNormNonnegative :
      0 ≤ fullGaussianLaplaceKernelNormalizationNorm :=
    norm_nonneg (((Real.pi : ℂ) / (1 : ℂ)) ^ (1 / 2 : ℂ))
  have hscaledBound :=
    mul_le_mul_of_nonneg_left hexponentialBound hbaseNormNonnegative
  calc
    ‖completedZeroNaturalScaleGaussian target rho n‖ =
        completedZeroNaturalScaleGaussianCoordinateNorm target rho n :=
      completedZeroNaturalScaleGaussian_norm_eq_coordinateNorm target rho n
    _ ≤ completedZeroScaledGaussianCoordinateNorm target rho 1 :=
      hscaledBound
    _ = completedZeroScaledGaussianNorm target rho 1 :=
      (fullGaussianLaplaceKernel_scaled_shift_norm_eq target rho 1).symm

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
