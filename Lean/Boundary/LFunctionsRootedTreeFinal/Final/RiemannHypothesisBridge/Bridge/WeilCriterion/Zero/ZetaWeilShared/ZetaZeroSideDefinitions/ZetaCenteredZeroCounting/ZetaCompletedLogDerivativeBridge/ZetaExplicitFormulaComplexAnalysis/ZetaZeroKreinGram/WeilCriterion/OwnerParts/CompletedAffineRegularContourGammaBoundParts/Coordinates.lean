import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner

/-!
# Coordinate transports for regular inverse-Gamma bounds

This file owns only the coordinate identities used by the compact-strip
inverse-Gamma bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The complex half has real part one half. -/
theorem regularInverseGamma_complexHalf_re :
    (1 / 2 : ℂ).re = (1 / 2 : ℝ) :=
  let halfAsOfReal : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
    (Complex.ofReal_div (1 : ℝ) (2 : ℝ)).symm
  Eq.trans
    (congrArg Complex.re halfAsOfReal)
    (Complex.ofReal_re (1 / 2 : ℝ))

/-- The complex half has zero imaginary part. -/
theorem regularInverseGamma_complexHalf_im :
    (1 / 2 : ℂ).im = 0 :=
  let halfAsOfReal : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
    (Complex.ofReal_div (1 : ℝ) (2 : ℝ)).symm
  Eq.trans
    (congrArg Complex.im halfAsOfReal)
    (Complex.ofReal_im (1 / 2 : ℝ))

/-- Multiplication by the real natural coordinate has the expected real part. -/
theorem regularInverseGamma_two_nat_complex_mul_re
    (n : ℕ) :
    (2 * (n : ℂ)).re = 2 * (n : ℝ) :=
  Eq.trans
    (Complex.mul_re (2 : ℂ) (n : ℂ))
    (Eq.trans
      (congrArg₂ HSub.hSub
        (congrArg₂ HMul.hMul
          (Complex.ofReal_re (2 : ℝ))
          (Complex.ofReal_re (n : ℝ)))
        (congrArg₂ HMul.hMul
          (Complex.ofReal_im (2 : ℝ))
          (Complex.ofReal_im (n : ℝ))))
      (Eq.trans
        (congrArg (fun value : ℝ => 2 * (n : ℝ) - value)
          (zero_mul (0 : ℝ)))
        (sub_zero (2 * (n : ℝ)))))

/-- Division by two places a complex point on the fixed line with half its
real and imaginary coordinates. -/
theorem regularInverseGamma_halfCoordinate
    (z : ℂ) :
    z / 2 =
      ((z.re / 2 : ℝ) : ℂ) +
        ((z.im / 2 : ℝ) : ℂ) * Complex.I :=
  let realPartEquality :
      (z / 2).re =
        (((z.re / 2 : ℝ) : ℂ) +
          ((z.im / 2 : ℝ) : ℂ) * Complex.I).re :=
    Eq.trans
      (Complex.div_ofReal_re z 2)
      (Eq.trans
        (ofReal_add_mul_I_re (z.re / 2) (z.im / 2)).symm
        (Eq.refl
          ((((z.re / 2 : ℝ) : ℂ) +
            ((z.im / 2 : ℝ) : ℂ) * Complex.I).re)))
  let imaginaryPartEquality :
      (z / 2).im =
        (((z.re / 2 : ℝ) : ℂ) +
          ((z.im / 2 : ℝ) : ℂ) * Complex.I).im :=
    Eq.trans
      (Complex.div_ofReal_im z 2)
      (Eq.trans
        (ofReal_add_mul_I_im (z.re / 2) (z.im / 2)).symm
        (Eq.refl
          ((((z.re / 2 : ℝ) : ℂ) +
            ((z.im / 2 : ℝ) : ℂ) * Complex.I).im)))
  Complex.ext realPartEquality imaginaryPartEquality

/-- The real coordinate of the shifted regular-strip point. -/
theorem regularInverseGamma_shiftedPoint_re
    (x T : ℝ) :
    ((1 / 2 : ℂ) + (x : ℂ) + (T : ℂ) * Complex.I).re =
      (1 / 2 : ℝ) + x :=
  Eq.trans
    (Complex.add_re ((1 / 2 : ℂ) + (x : ℂ))
      ((T : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd
        (Eq.trans
          (Complex.add_re (1 / 2 : ℂ) (x : ℂ))
          (congrArg₂ HAdd.hAdd
            regularInverseGamma_complexHalf_re
            (Complex.ofReal_re x)))
        (ofReal_mul_I_re_zero T))
      (add_zero ((1 / 2 : ℝ) + x)))

/-- The imaginary coordinate of the shifted regular-strip point. -/
theorem regularInverseGamma_shiftedPoint_im
    (x T : ℝ) :
    ((1 / 2 : ℂ) + (x : ℂ) + (T : ℂ) * Complex.I).im = T :=
  Eq.trans
    (Complex.add_im ((1 / 2 : ℂ) + (x : ℂ))
      ((T : ℂ) * Complex.I))
    (Eq.trans
      (congrArg₂ HAdd.hAdd
        (Eq.trans
          (Complex.add_im (1 / 2 : ℂ) (x : ℂ))
          (congrArg₂ HAdd.hAdd
            regularInverseGamma_complexHalf_im
            (Complex.ofReal_im x)))
        (ofReal_mul_I_im T))
      (Eq.trans (congrArg (fun value : ℝ => value + T) (zero_add 0))
        (zero_add T)))

/-- Adding one half to the centered real coordinate returns the original
complex real coordinate. -/
theorem regularInverseGamma_half_add_centered_real_eq
    (x : ℝ) :
    (1 / 2 : ℂ) + ((x - (1 / 2 : ℝ) : ℝ) : ℂ) = (x : ℂ) :=
  let realEquality :
      (1 / 2 : ℝ) + (x - (1 / 2 : ℝ)) = x :=
    Eq.trans
      (add_comm (1 / 2 : ℝ) (x - (1 / 2 : ℝ)))
      (sub_add_cancel x (1 / 2 : ℝ))
  let complexSumEquality :
      (1 / 2 : ℂ) + ((x - (1 / 2 : ℝ) : ℝ) : ℂ) =
        (((1 / 2 : ℝ) + (x - (1 / 2 : ℝ)) : ℝ) : ℂ) :=
    let halfAsOfReal : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
      (Complex.ofReal_div (1 : ℝ) (2 : ℝ)).symm
    Eq.trans
      (congrArg
        (fun value : ℂ => value + ((x - (1 / 2 : ℝ) : ℝ) : ℂ))
        halfAsOfReal)
      (Complex.ofReal_add (1 / 2 : ℝ) (x - (1 / 2 : ℝ))).symm
  Eq.trans complexSumEquality
    (congrArg (fun value : ℝ => (value : ℂ)) realEquality)

/-- The top horizontal path is the shifted regular-strip point. -/
theorem regularInverseGamma_topPath_eq_shiftedCenteredPoint
    (family : ExplicitFormulaContourFamily) (x T : ℝ) :
    zetaCompletedExplicitFormulaTopPath (family.rectangle T) x =
      (1 / 2 : ℂ) + ((x - (1 / 2 : ℝ) : ℝ) : ℂ) +
        (T : ℂ) * Complex.I :=
  Eq.trans
    (show zetaCompletedExplicitFormulaTopPath (family.rectangle T) x =
      (x : ℂ) + (T : ℂ) * Complex.I from rfl)
    (congrArg (fun value : ℂ => value + (T : ℂ) * Complex.I)
      (regularInverseGamma_half_add_centered_real_eq x).symm)

/-- The bottom horizontal path is the shifted regular-strip point with
reflected height. -/
theorem regularInverseGamma_bottomPath_eq_shiftedCenteredPoint
    (family : ExplicitFormulaContourFamily) (x T : ℝ) :
    zetaCompletedExplicitFormulaBottomPath (family.rectangle T) x =
      (1 / 2 : ℂ) + ((x - (1 / 2 : ℝ) : ℝ) : ℂ) +
        ((-T : ℝ) : ℂ) * Complex.I :=
  Eq.trans
    (show zetaCompletedExplicitFormulaBottomPath (family.rectangle T) x =
      (x : ℂ) - (T : ℂ) * Complex.I from rfl)
    (Eq.trans
      (Eq.trans
        (sub_eq_add_neg (x : ℂ) ((T : ℂ) * Complex.I))
        (Eq.trans
          (congrArg (fun value : ℂ => (x : ℂ) + value)
            (neg_mul (T : ℂ) Complex.I).symm)
          (congrArg
            (fun value : ℂ => (x : ℂ) + value * Complex.I)
            (Complex.ofReal_neg T).symm)))
      (congrArg (fun value : ℂ => value + ((-T : ℝ) : ℂ) * Complex.I)
        (regularInverseGamma_half_add_centered_real_eq x).symm))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
