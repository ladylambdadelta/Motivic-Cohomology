import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ResidualCoordinate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.PositiveRealWindowLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part07

/-!
# Positive real-window limit source

This file owns convergence of positive prime-defect real windows to the owner
positive channel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Source convergence of positive prime-defect real windows to the raw
positive coordinate presentation. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsumRe_source_primitive
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
    f
    hmajorant

/-- Source reconstruction of the raw positive coordinate total as the owner
completed positive prime-defect channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_windowLimit_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsumRe_source_primitive
      f hmajorant
  let howner :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_positiveRealWindowLimit
      f hmajorant hcoordinateZero
  tendsto_nhds_unique hcoordinate howner

/-- Source reconstruction of the raw positive coordinate total as the owner
completed positive prime-defect channel, with the positive/off-diagonal gap
vanishing as the explicit upstream input. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_positiveOffDiagonalGap_eq_zero_windowLimit_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  let hdiagonalZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 :=
    let hgapResidual :
        completedPrimePositiveOffDiagonalGap f =
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
      completedPrimePositiveOffDiagonalGap_eq_diagonalDebtCoordinateTsum_re_summedTransport
        f D hmajorant
    hgapResidual.symm.trans hgapZero
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_windowLimit_source
    f hmajorant hdiagonalZero

/-- Source convergence of positive prime-defect real windows to the owner
positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_source_primitive
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_positiveRealWindowLimit
    f hmajorant
    hcoordinateZero

/-- Source convergence of positive prime-defect real windows to the owner
positive channel, with the positive/off-diagonal gap vanishing explicitly
supplied. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_of_positiveOffDiagonalGap_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
  let hdiagonalZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 :=
    let hgapResidual :
        completedPrimePositiveOffDiagonalGap f =
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
      completedPrimePositiveOffDiagonalGap_eq_diagonalDebtCoordinateTsum_re_summedTransport
        f D hmajorant
    hgapResidual.symm.trans hgapZero
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_source_primitive
    f hmajorant hdiagonalZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
