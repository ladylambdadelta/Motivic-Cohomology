import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ResidualCoordinate

/-!
# Diagonal-debt scalar split source

This file owns the owner scalar identity splitting completed diagonal debt into
the positive channel plus the completed two-face real coefficient.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Source scalar split for the owner completed diagonal-debt real part. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_positiveChannel_add_twoFace_re_source_primitive
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedPrimeDefectKernelPositiveChannel f +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let hpositive :
      completedPrimeDefectKernelPositiveChannel f = Complex.re P :=
    Eq.refl (completedPrimeDefectKernelPositiveChannel f)
  let htwoFace :
      Complex.re T =
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    Eq.refl (Complex.re T)
  let hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        Complex.re D :=
    Eq.refl (Complex.re D)
  let hexpansion :
      P + T = D :=
    zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms
      f
  let hrealExpansion :
      Complex.re D = Complex.re (P + T) :=
    congrArg Complex.re hexpansion.symm
  let hrealAdd :
      Complex.re (P + T) = Complex.re P + Complex.re T :=
    Complex.add_re P T
  let htwoFaceAdd :
      Complex.re P + Complex.re T =
        Complex.re P +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg
      (fun value : ℝ => Complex.re P + value)
      htwoFace
  let hpositiveAdd :
      Complex.re P +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        completedPrimeDefectKernelPositiveChannel f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg
      (fun value : ℝ =>
        value + Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
      hpositive.symm
  Eq.trans hdiagonal
    (Eq.trans hrealExpansion
      (Eq.trans hrealAdd
        (Eq.trans htwoFaceAdd hpositiveAdd)))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
