import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceTransportParts.DiagonalOwnerLimitConditional

/-!
# Conditional completed prime trace transport

This file exposes completed prime trace transport from explicit completed
diagonal-debt real-coordinate `HasSum` inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs transport the raw
diagonal-debt coordinate presentation to the owner completed diagonal-debt
scalar at the trace-transport source level. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_core
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝
          (Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f hmajorant
  let howner :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_limit_core
      f C Creflect hhasSum hhasSumReflect
  tendsto_nhds_unique hcoordinate howner

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give source owner
transport for the completed prime-defect residual coordinates. -/
theorem completedPrimeDefectCoordinateOwnerTransport_of_diagonalDebtCoordinate_re_hasSum_traceTransport_source_core
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    CompletedPrimeDefectCoordinateOwnerTransport f :=
  And.intro
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_traceTransport_source_core
      f)
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_core
      f C Creflect hhasSum hhasSumReflect)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give the source
owner limit of completed diagonal-debt real windows. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_core
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_limit_core
    f C Creflect hhasSum hhasSumReflect

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs transport the raw
positive coordinate presentation to the owner completed positive prime-defect
channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_diagonalDebtCoordinate_re_hasSum_source_core
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
    f
    hmajorant
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_core
      f C Creflect hhasSum hhasSumReflect)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
