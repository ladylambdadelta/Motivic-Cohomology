import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ArchimedeanCriticalLineProduct
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.LogDerivativeFiniteFormula

/-!
# Gamma logarithmic derivative on the centered critical line

The completed real Gamma factor is regular on `1 / 2 + it`. Its half argument
is the positive fixed line `1 / 4 + (t / 2)i`, so the direct finite
Abel-Plana logarithmic-derivative formula applies without contour data.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

/-- The real coordinate of the complex half is the real half. -/
private theorem zetaCompletedComplexHalf_re :
    (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by
  have hhalf_complex : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
    Eq.symm (Complex.ofReal_div (1 : ℝ) (2 : ℝ))
  have hhalf_coe_re : (((1 / 2 : ℝ) : ℂ).re) = (1 / 2 : ℝ) :=
    Complex.ofReal_re (1 / 2 : ℝ)
  exact Eq.trans (congrArg Complex.re hhalf_complex) hhalf_coe_re

/-- The centered critical line has real part one half. -/
theorem zetaCompletedCenteredSpectralLine_re (t : ℝ) :
    (zetaCompletedCenteredSpectralLine t).re = (1 / 2 : ℝ) := by
  calc
    (zetaCompletedCenteredSpectralLine t).re =
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re := by
      exact Eq.refl _
    _ = (1 / 2 : ℂ).re + ((t : ℂ) * Complex.I).re := by
      exact Complex.add_re (1 / 2 : ℂ) ((t : ℂ) * Complex.I)
    _ = (1 / 2 : ℝ) + 0 := by
      exact congrArg₂ Add.add
        zetaCompletedComplexHalf_re
        (zetaCompletedImaginarySpectralCoordinate_re t)
    _ = (1 / 2 : ℝ) :=
      add_zero (1 / 2 : ℝ)

/-- Every centered critical-line point has positive real part. -/
theorem zetaCompletedCenteredSpectralLine_re_pos (t : ℝ) :
    0 < (zetaCompletedCenteredSpectralLine t).re := by
  exact Eq.subst
    (motive := fun value : ℝ => 0 < value)
    (zetaCompletedCenteredSpectralLine_re t).symm
    one_half_pos

/-- A centered critical-line point cannot be a nonpositive even integer. -/
theorem zetaCompletedCenteredSpectralLine_ne_GammaReal_singular
    (t : ℝ) (n : ℕ) :
    zetaCompletedCenteredSpectralLine t ≠ -(2 * (n : ℂ)) := by
  intro equality
  have realEquality := congrArg Complex.re equality
  have leftPositive : 0 < (zetaCompletedCenteredSpectralLine t).re :=
    zetaCompletedCenteredSpectralLine_re_pos t
  have naturalRealNonnegative : 0 ≤ ((n : ℕ) : ℝ) :=
    Nat.cast_nonneg n
  have rightNonpositive :
      (-(2 * (n : ℂ))).re ≤ 0 := by
    have rightReal :
        (-(2 * (n : ℂ))).re = -(2 * (n : ℝ)) := by
      calc
        (-(2 * (n : ℂ))).re = -(2 * (n : ℂ)).re := by
          exact Complex.neg_re (2 * (n : ℂ))
        _ = -(2 * (n : ℂ).re) := by
          exact congrArg Neg.neg (Complex.mul_re (2 : ℂ) (n : ℂ) |>.trans
            (Eq.trans
              (congrArg₂ Sub.sub
                (congrArg₂ Mul.mul (Complex.ofReal_re 2)
                  (Complex.ofReal_re (n : ℝ)))
                (congrArg₂ Mul.mul (Complex.ofReal_im 2)
                  (Complex.ofReal_im (n : ℝ))))
              (Eq.trans
                (congrArg₂ Sub.sub (Eq.refl (2 * (n : ℝ)))
                  (zero_mul (0 : ℝ)))
                (sub_zero (2 * (n : ℝ))))))
        _ = -(2 * (n : ℝ)) := by
          exact congrArg (fun value : ℝ => -(2 * value))
            (Complex.ofReal_re (n : ℝ))
    exact Eq.subst
      (motive := fun value : ℝ => value ≤ 0)
      rightReal.symm
      (neg_nonpos.mpr (mul_nonneg zero_le_two naturalRealNonnegative))
  have leftNonpositive :
      (zetaCompletedCenteredSpectralLine t).re ≤ 0 :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ 0)
      realEquality.symm
      rightNonpositive
  exact (not_lt_of_ge leftNonpositive) leftPositive

/-- Deligne's real Gamma factor is nonzero on the centered critical line. -/
theorem zetaCompletedCenteredSpectralLine_GammaReal_ne_zero (t : ℝ) :
    Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) ≠ 0 := by
  exact Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedCenteredSpectralLine t)
    (zetaCompletedCenteredSpectralLine_re_pos t)

/-- Deligne's real Gamma factor is differentiable on the centered critical
line. -/
theorem zetaCompletedCenteredSpectralLine_GammaReal_differentiableAt
    (t : ℝ) :
    DifferentiableAt ℂ Complex.Gammaℝ
      (zetaCompletedCenteredSpectralLine t) := by
  exact Gammaℝ_differentiableAt_of_ne_zero_locus
    (zetaCompletedCenteredSpectralLine_ne_GammaReal_singular t)

/-- The inverse-completion logarithmic derivative on the centered line is the
negative logarithmic derivative of `Gammaℝ`. -/
theorem inverseGammaCompletionLogDeriv_centeredSpectralLine_eq
    (t : ℝ) :
    inverseGammaCompletionLogDeriv (zetaCompletedCenteredSpectralLine t) =
      -deriv Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) /
        Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) := by
  exact inverseGammaCompletionLogDeriv_eq_neg_Gammaℝ_logDeriv
    (zetaCompletedCenteredSpectralLine_GammaReal_differentiableAt t)
    (zetaCompletedCenteredSpectralLine_GammaReal_ne_zero t)

/-- Halving a centered critical-line point gives the positive quarter-line. -/
theorem zetaCompletedCenteredSpectralLine_half_eq_quarterLine (t : ℝ) :
    zetaCompletedCenteredSpectralLine t / 2 =
      ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
  calc
    zetaCompletedCenteredSpectralLine t / 2 =
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) / 2 := by
      exact Eq.refl _
    _ = (1 / 2 : ℂ) / 2 + ((t : ℂ) * Complex.I) / 2 := by
      exact add_div (1 / 2 : ℂ) ((t : ℂ) * Complex.I) 2
    _ = (1 / 4 : ℂ) + ((t : ℂ) / 2) * Complex.I := by
      have twoTimesTwo : (2 : ℂ) * 2 = 4 := by
        exact
          Eq.trans
            (Complex.ofReal_mul (2 : ℝ) (2 : ℝ)).symm
            (congrArg (fun value : ℝ => (value : ℂ)) Real.two_mul_two_eq_four)
      have quarterEquality : (1 / 2 : ℂ) / 2 = (1 / 4 : ℂ) := by
        exact Eq.trans
          (div_div (1 : ℂ) 2 2)
          (congrArg (fun denominator : ℂ => (1 : ℂ) / denominator)
            twoTimesTwo)
      exact congrArg₂ Add.add quarterEquality
        (mul_div_right_comm (t : ℂ) Complex.I 2)
    _ = ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
      exact congrArg₂ Add.add
        (Complex.ofReal_div (1 : ℝ) 4).symm
        (congrArg (fun height : ℂ => height * Complex.I)
          (Complex.ofReal_div t 2).symm)

/-- The `Gammaℝ` logarithmic derivative on the centered line is the
elementary pi term plus the ordinary Gamma logarithmic derivative on the
quarter-line. -/
theorem GammaReal_logDerivative_centeredSpectralLine_eq_quarterLine
    (t : ℝ) :
    deriv Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) /
        Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) =
      Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
        (deriv Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) * (1 / 2 : ℂ)) /
          Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) := by
  have decomposition :=
    Gammaℝ_logDeriv_eq_pi_add_halfGamma_logDeriv
      (zetaCompletedCenteredSpectralLine_ne_GammaReal_singular t)
      (zetaCompletedCenteredSpectralLine_GammaReal_ne_zero t)
  have halfEquality :=
    zetaCompletedCenteredSpectralLine_half_eq_quarterLine t
  exact Eq.trans decomposition
    (congrArg
      (fun halfPoint : ℂ =>
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
          (deriv Complex.Gamma halfPoint * (1 / 2 : ℂ)) /
            Complex.Gamma halfPoint)
      halfEquality)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
