import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ResidualCoordinate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalDebtAnnihilatorGapAssembly

/-!
# Completed two-face real transport source

This file owns the real-part transport from the completed two-face GNS matrix
coefficient to the raw lower-weight two-face coefficient.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Source real-part transport for the completed two-face GNS matrix
coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_source_primitive
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hcompleted :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f
  let hraw :
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
      f
  hcompleted.trans hraw.symm

/-- Source real-part transport for the completed two-face GNS matrix
coefficient, with the positive/off-diagonal gap vanishing explicitly supplied. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_of_positiveOffDiagonalGap_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hcompleted :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f
  let hraw :
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
      f
  hcompleted.trans hraw.symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
