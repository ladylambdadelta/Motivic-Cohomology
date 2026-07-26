import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineArchimedeanBinet

/-!
# Positive-half-plane Binet conjugation core

Explicit coordinate and principal-log-cut facts used by the affine
finite-Binet conjugation owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The explicit fixed-real-part vertical line has real coordinate `sigma`. -/
theorem fixedRealPartLine_re_explicit
    (sigma t : ℝ) :
    (((sigma : ℂ) + (t : ℂ) * Complex.I).re) = sigma :=
  Complex.fixedRealPartLine_re sigma t

/-- The explicit fixed-real-part vertical line has imaginary coordinate `t`. -/
theorem fixedRealPartLine_im_explicit
    (sigma t : ℝ) :
    (((sigma : ℂ) + (t : ℂ) * Complex.I).im) = t :=
  let split :
      (((sigma : ℂ) + (t : ℂ) * Complex.I).im) =
        (sigma : ℂ).im + ((t : ℂ) * Complex.I).im :=
    Complex.add_im (sigma : ℂ) ((t : ℂ) * Complex.I)
  let realPart :
      (sigma : ℂ).im = 0 :=
    Complex.ofReal_im sigma
  let imaginaryPart :
      ((t : ℂ) * Complex.I).im = t :=
    Eq.trans (Complex.mul_I_im (t : ℂ)) (Complex.ofReal_re t)
  let combine :
      (sigma : ℂ).im + ((t : ℂ) * Complex.I).im =
        0 + t :=
    congrArg₂ HAdd.hAdd realPart imaginaryPart
  Eq.trans split
    (Eq.trans combine (zero_add t))

/-- Opposite heights on a fixed real-part line are conjugates. -/
theorem fixedRealPartLine_neg_eq_star
    (sigma t : ℝ) :
    ((sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
      star ((sigma : ℂ) + (t : ℂ) * Complex.I) :=
  let realEquality :
      (((sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I).re) =
        (star ((sigma : ℂ) + (t : ℂ) * Complex.I)).re :=
    Eq.trans
      (fixedRealPartLine_re_explicit sigma (-t))
      (Eq.trans
        (fixedRealPartLine_re_explicit sigma t).symm
        rfl)
  let imaginaryEquality :
      (((sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I).im) =
        (star ((sigma : ℂ) + (t : ℂ) * Complex.I)).im :=
    Eq.trans
      (fixedRealPartLine_im_explicit sigma (-t))
      (Eq.trans
        (congrArg Neg.neg
          (fixedRealPartLine_im_explicit sigma t).symm)
        rfl)
  Complex.ext realEquality imaginaryEquality

/-- A fixed line in the open right half-plane avoids the principal-log cut. -/
theorem fixedRealPartLine_arg_ne_pi
    {sigma t : ℝ}
    (sigmaPositive : 0 < sigma) :
    Complex.arg (sigma + t * Complex.I : ℂ) ≠ Real.pi :=
  fun argumentEquality =>
  let negativeRealPart :
      (sigma + t * Complex.I : ℂ).re < 0 :=
    (Complex.arg_eq_pi_iff.mp argumentEquality).1
  let realPartEquality :
      (sigma + t * Complex.I : ℂ).re = sigma :=
    Complex.fixedRealPartLine_re sigma t
  let sigmaNegative : sigma < 0 :=
    Eq.subst
      (motive := fun value : ℝ => value < 0)
      realPartEquality
      negativeRealPart
  (not_lt_of_ge (le_of_lt sigmaPositive)) sigmaNegative

/-- Principal logarithms at opposite heights on a positive fixed line are
conjugates. -/
theorem fixedRealPartLine_log_neg_eq_star
    {sigma t : ℝ}
    (sigmaPositive : 0 < sigma) :
    Complex.log ((sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
      star (Complex.log ((sigma : ℂ) + (t : ℂ) * Complex.I)) :=
  let point : ℂ := (sigma : ℂ) + (t : ℂ) * Complex.I
  let lineEquality :
      ((sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) = star point :=
    fixedRealPartLine_neg_eq_star sigma t
  let avoidsCut : Complex.arg point ≠ Real.pi :=
    fixedRealPartLine_arg_ne_pi sigmaPositive
  Eq.trans
    (congrArg Complex.log lineEquality)
    (Complex.log_conj point avoidsCut)

/-- The fixed-vertical Binet main term at opposite heights is conjugate. -/
theorem gammaLogDerivativeFixedVerticalMain_neg_eq_star
    {sigma t : ℝ}
    (sigmaPositive : 0 < sigma) :
    Complex.GammaLogDerivativeFixedVerticalMain sigma (-t) =
      star (Complex.GammaLogDerivativeFixedVerticalMain sigma t) :=
  let point : ℂ := (sigma : ℂ) + (t : ℂ) * Complex.I
  let reflectedPoint : ℂ := (sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I
  let pointEquality : reflectedPoint = star point :=
    fixedRealPartLine_neg_eq_star sigma t
  let logarithmEquality :
      Complex.log reflectedPoint = star (Complex.log point) :=
    fixedRealPartLine_log_neg_eq_star sigmaPositive
  let twoStar : star (2 : ℂ) = (2 : ℂ) :=
    star_ofNat 2
  let denominatorStar :
      star ((2 : ℂ) * point) = (2 : ℂ) * star point :=
    Eq.trans
      (star_mul (2 : ℂ) point)
      (Eq.trans
        (congrArg (fun value : ℂ => star point * value) twoStar)
        (mul_comm (star point) (2 : ℂ)))
  let reciprocalStar :
      star (1 / ((2 : ℂ) * point)) =
        1 / ((2 : ℂ) * star point) :=
    Eq.trans (star_div₀ (1 : ℂ) ((2 : ℂ) * point))
      (congrArg₂ HDiv.hDiv (star_one (R := ℂ)) denominatorStar)
  let reciprocalEquality :
      1 / ((2 : ℂ) * reflectedPoint) =
        star (1 / ((2 : ℂ) * point)) :=
    Eq.trans
      (congrArg
        (fun value : ℂ => 1 / ((2 : ℂ) * value))
        pointEquality)
      reciprocalStar.symm
  let leftDefinition :
      Complex.GammaLogDerivativeFixedVerticalMain sigma (-t) =
        Complex.log reflectedPoint - 1 / ((2 : ℂ) * reflectedPoint) :=
    rfl
  let subtractionEquality :
      Complex.log reflectedPoint - 1 / ((2 : ℂ) * reflectedPoint) =
        star (Complex.log point) -
          star (1 / ((2 : ℂ) * point)) :=
    congrArg₂ HSub.hSub logarithmEquality reciprocalEquality
  let starSubtraction :
      star (Complex.log point) - star (1 / ((2 : ℂ) * point)) =
        star (Complex.log point - 1 / ((2 : ℂ) * point)) :=
    (star_sub
      (Complex.log point)
      (1 / ((2 : ℂ) * point))).symm
  let rightDefinition :
      star (Complex.log point - 1 / ((2 : ℂ) * point)) =
        star (Complex.GammaLogDerivativeFixedVerticalMain sigma t) :=
    congrArg star
      (show Complex.GammaLogDerivativeFixedVerticalMain sigma t =
        Complex.log point - 1 / ((2 : ℂ) * point) from rfl).symm
  Eq.trans leftDefinition
    (Eq.trans subtractionEquality
      (Eq.trans starSubtraction rightDefinition))

/-- The real `pi` logarithmic-derivative constant is fixed by conjugation. -/
theorem gammaRealPiLogDerivativeTerm_star :
    star zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm =
      zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm :=
  let logarithmEquality :
      Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log (le_of_lt Real.pi_pos)).symm
  let logarithmStar :
      star (Complex.log (Real.pi : ℂ)) =
        Complex.log (Real.pi : ℂ) :=
    Eq.trans
      (congrArg star logarithmEquality)
      (Eq.trans
        (Complex.conj_ofReal (Real.log Real.pi))
        logarithmEquality.symm)
  let halfStar : star (1 / 2 : ℂ) = (1 / 2 : ℂ) :=
    Eq.trans (star_div₀ (1 : ℂ) (2 : ℂ))
      (congrArg₂ HDiv.hDiv
        (star_one (R := ℂ))
        (star_ofNat 2))
  let negativeHalfStar :
      star (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) :=
    Eq.trans (star_neg (1 / 2 : ℂ))
      (congrArg Neg.neg halfStar)
  Eq.trans
    (star_mul
      (Complex.log (Real.pi : ℂ))
      (-(1 / 2 : ℂ)))
    (Eq.trans
      (congrArg₂ HMul.hMul negativeHalfStar logarithmStar)
      (mul_comm (-(1 / 2 : ℂ)) (Complex.log (Real.pi : ℂ))))

/-- The scalar integrand in the differentiated Abel--Plana remainder. -/
noncomputable def gammaLogDerivativeFixedVerticalRemainderIntegrand
    (sigma t u : ℝ) : ℂ :=
  (-(u : ℂ) /
      ((sigma + t * Complex.I : ℂ) ^ 2 + (u : ℂ) ^ 2)) /
    (Complex.exp (((2 : ℝ) * Real.pi * u : ℝ) : ℂ) - 1)

/-- The differentiated Abel--Plana remainder integrand at opposite heights
is conjugate. -/
theorem gammaLogDerivativeFixedVerticalRemainderIntegrand_neg_eq_star
    (sigma t u : ℝ) :
    gammaLogDerivativeFixedVerticalRemainderIntegrand sigma (-t) u =
      star (gammaLogDerivativeFixedVerticalRemainderIntegrand sigma t u) :=
  let point : ℂ := (sigma : ℂ) + (t : ℂ) * Complex.I
  let reflectedPoint : ℂ := (sigma : ℂ) + ((-t : ℝ) : ℂ) * Complex.I
  let realU : ℂ := (u : ℂ)
  let thermalArgument : ℂ :=
    (((2 : ℝ) * Real.pi * u : ℝ) : ℂ)
  let pointEquality : reflectedPoint = star point :=
    fixedRealPartLine_neg_eq_star sigma t
  let realUStar : star realU = realU :=
    Complex.conj_ofReal u
  let thermalArgumentStar :
      star thermalArgument = thermalArgument :=
    Complex.conj_ofReal ((2 : ℝ) * Real.pi * u)
  let pointSquareStar :
      star (point ^ 2) = (star point) ^ 2 :=
    star_pow point 2
  let realUSquareStar :
      star (realU ^ 2) = realU ^ 2 :=
    Eq.trans (star_pow realU 2)
      (congrArg (fun value : ℂ => value ^ 2) realUStar)
  let quadraticEquality :
      reflectedPoint ^ 2 + realU ^ 2 =
        star (point ^ 2 + realU ^ 2) :=
    Eq.trans
      (congrArg
          (fun value : ℂ => value ^ 2 + realU ^ 2)
          pointEquality)
      (Eq.trans
        (congrArg₂ HAdd.hAdd pointSquareStar.symm
          realUSquareStar.symm)
        (star_add (point ^ 2) (realU ^ 2)).symm)
  let numeratorStar : star (-realU) = -realU :=
    Eq.trans (star_neg realU)
      (congrArg Neg.neg realUStar)
  let firstQuotientEquality :
      (-realU) / (reflectedPoint ^ 2 + realU ^ 2) =
        star ((-realU) / (point ^ 2 + realU ^ 2)) :=
    Eq.trans
      (congrArg
        (fun denominator : ℂ => (-realU) / denominator)
        quadraticEquality)
      (Eq.trans
        (congrArg
          (fun numerator : ℂ => numerator /
            star (point ^ 2 + realU ^ 2))
          numeratorStar.symm)
        (star_div₀
          (-realU)
          (point ^ 2 + realU ^ 2)).symm)
  let exponentialStar :
      star (Complex.exp thermalArgument) =
        Complex.exp thermalArgument :=
    let conjugateExponential :
        Complex.exp (star thermalArgument) =
          star (Complex.exp thermalArgument) :=
      Complex.exp_conj thermalArgument
    Eq.trans conjugateExponential.symm
      (congrArg Complex.exp thermalArgumentStar)
  let oneStar : star (1 : ℂ) = (1 : ℂ) :=
    star_one (R := ℂ)
  let thermalDenominatorStar :
      star (Complex.exp thermalArgument - 1) =
        Complex.exp thermalArgument - 1 :=
    Eq.trans
      (star_sub (Complex.exp thermalArgument) (1 : ℂ))
      (congrArg₂ HSub.hSub exponentialStar oneStar)
  let numeratorTransport :
      gammaLogDerivativeFixedVerticalRemainderIntegrand sigma (-t) u =
        star ((-realU) / (point ^ 2 + realU ^ 2)) /
          (Complex.exp thermalArgument - 1) :=
    congrArg
        (fun numerator : ℂ =>
          numerator / (Complex.exp thermalArgument - 1))
        firstQuotientEquality
  let denominatorTransport :
      star ((-realU) / (point ^ 2 + realU ^ 2)) /
          (Complex.exp thermalArgument - 1) =
        star ((-realU) / (point ^ 2 + realU ^ 2)) /
          star (Complex.exp thermalArgument - 1) :=
    congrArg
        (fun denominator : ℂ =>
          star ((-realU) / (point ^ 2 + realU ^ 2)) /
            denominator)
        thermalDenominatorStar.symm
  let quotientStar :
      star ((-realU) / (point ^ 2 + realU ^ 2)) /
          star (Complex.exp thermalArgument - 1) =
        star
        (((-realU) / (point ^ 2 + realU ^ 2)) /
          (Complex.exp thermalArgument - 1)) :=
    (star_div₀
      ((-realU) / (point ^ 2 + realU ^ 2))
      (Complex.exp thermalArgument - 1)).symm
  let rightDefinition :
      star
        (((-realU) / (point ^ 2 + realU ^ 2)) /
          (Complex.exp thermalArgument - 1)) =
        star (gammaLogDerivativeFixedVerticalRemainderIntegrand sigma t u) :=
    rfl
  Eq.trans numeratorTransport
    (Eq.trans denominatorTransport
      (Eq.trans quotientStar rightDefinition))

/-- The differentiated Abel--Plana remainder at opposite heights is
conjugate. -/
theorem gammaLogDerivativeFixedVerticalRemainder_neg_eq_star
    (sigma t : ℝ) :
    Complex.GammaLogDerivativeFixedVerticalRemainder sigma (-t) =
      star (Complex.GammaLogDerivativeFixedVerticalRemainder sigma t) :=
  let integrand : ℝ → ℝ → ℂ :=
    gammaLogDerivativeFixedVerticalRemainderIntegrand sigma
  let functionEquality :
      integrand (-t) = fun u : ℝ => star (integrand t u) :=
    funext
      (fun u : ℝ =>
        gammaLogDerivativeFixedVerticalRemainderIntegrand_neg_eq_star
          sigma t u)
  let integralEquality :
      (∫ u : ℝ in Set.Ioi (0 : ℝ), integrand (-t) u) =
        star (∫ u : ℝ in Set.Ioi (0 : ℝ), integrand t u) :=
    Eq.trans
      (congrArg
        (fun candidate : ℝ → ℂ =>
          ∫ u : ℝ in Set.Ioi (0 : ℝ), candidate u)
        functionEquality)
      integral_conj
  let twoStar : star (2 : ℂ) = (2 : ℂ) :=
    star_ofNat 2
  let leftDefinition :
      Complex.GammaLogDerivativeFixedVerticalRemainder sigma (-t) =
        2 * ∫ u : ℝ in Set.Ioi (0 : ℝ), integrand (-t) u :=
    rfl
  let integralTransport :
      2 * ∫ u : ℝ in Set.Ioi (0 : ℝ), integrand (-t) u =
        2 * star (∫ u : ℝ in Set.Ioi (0 : ℝ), integrand t u) :=
    congrArg (fun value : ℂ => (2 : ℂ) * value) integralEquality
  let coefficientTransport :
      2 * star (∫ u : ℝ in Set.Ioi (0 : ℝ), integrand t u) =
        star
          (2 * ∫ u : ℝ in Set.Ioi (0 : ℝ), integrand t u) :=
    Eq.trans
      (mul_comm
        (2 : ℂ)
        (star (∫ u : ℝ in Set.Ioi (0 : ℝ), integrand t u)))
      (Eq.trans
        (congrArg
          (fun coefficient : ℂ =>
            star (∫ u : ℝ in Set.Ioi (0 : ℝ), integrand t u) *
              coefficient)
          twoStar.symm)
        (star_mul
          (2 : ℂ)
          (∫ u : ℝ in Set.Ioi (0 : ℝ), integrand t u)).symm)
  let rightDefinition :
      star
          (2 * ∫ u : ℝ in Set.Ioi (0 : ℝ), integrand t u) =
        star (Complex.GammaLogDerivativeFixedVerticalRemainder sigma t) :=
    congrArg star
      (show Complex.GammaLogDerivativeFixedVerticalRemainder sigma t =
        2 * ∫ u : ℝ in Set.Ioi (0 : ℝ), integrand t u from rfl).symm
  Eq.trans leftDefinition
    (Eq.trans integralTransport
      (Eq.trans coefficientTransport rightDefinition))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
