import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ResidualCoordinate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part06
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalDebtAnnihilatorGapAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.PositiveRealWindowLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ResidualCoordinateSource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.VisibleRemainderConvergence

/-!
# Positive coordinate owner transport

This file owns the lower-level transport from diagonal-coordinate vanishing to
positive-coordinate owner reconstruction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed off-diagonal trace scalar is the owner completed positive
channel. -/
theorem completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_source
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f :=
  completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_twoFaceZero_source f

/-- The completed off-diagonal trace scalar is the owner completed positive
channel, with diagonal-coordinate vanishing explicitly supplied. -/
theorem completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_of_coordinatePositive_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f :=
  let hcoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_diagonalDebtCoordinateTsum_re_eq_zero
      f D hmajorant hcoordinateZero
  let howner :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_windowLimit_source
      f hmajorant hcoordinateZero
  hcoordinate.trans howner

/-- The completed positive prime-defect coordinate total reconstructs the
owner completed positive prime-defect channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_source_primitive
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_windowLimit_source
    f hmajorant hcoordinateZero

/-- The completed positive prime-defect coordinate total reconstructs the
owner completed positive prime-defect channel, with positive/off-diagonal gap
vanishing explicitly supplied. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_positiveOffDiagonalGap_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_positiveOffDiagonalGap_eq_zero_windowLimit_source
    f D hmajorant hgapZero

/-- Positive/off-diagonal gap vanishing and lower-weight normalization
annihilate the raw completed positive coordinate trace. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_of_positiveOffDiagonalGap_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  let hpositiveOwner :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_positiveOffDiagonalGap_eq_zero_source_primitive
      f D hmajorant hgapZero
  let hownerZero :
      completedPrimeDefectKernelPositiveChannel f = 0 :=
    completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f
  hpositiveOwner.trans hownerZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
