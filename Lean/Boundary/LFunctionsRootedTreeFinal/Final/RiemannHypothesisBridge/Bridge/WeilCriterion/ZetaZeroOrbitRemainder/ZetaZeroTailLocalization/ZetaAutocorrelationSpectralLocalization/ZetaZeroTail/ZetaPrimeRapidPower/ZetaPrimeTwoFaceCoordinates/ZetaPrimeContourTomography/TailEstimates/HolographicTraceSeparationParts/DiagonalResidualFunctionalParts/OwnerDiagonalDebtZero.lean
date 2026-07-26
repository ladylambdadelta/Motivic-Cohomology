import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.CompletedTwoFaceRealTransport

/-!
# Owner diagonal-debt zero source

This file owns vanishing of the owner completed diagonal-debt scalar.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Source lower-weight annihilation of the owner completed diagonal-debt
prime-defect scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
    f
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_source_primitive
      f hmajorant hcoordinateZero)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
