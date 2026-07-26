import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.PositiveRealWindowLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.PositiveRealWindowLimitConditional

/-!
# Conditional positive real-window limit source

This file isolates the explicit `HasSum` compatibility layer for positive
real-window transport. The active owner file keeps only coordinate-zero and
gap-zero inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give convergence of
positive prime-defect real windows to the raw positive coordinate
presentation. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsumRe_of_diagonalDebtCoordinate_re_hasSum_source_primitive
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
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
    f hmajorant

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs reconstruct the raw
positive coordinate total as the owner completed positive prime-defect
channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_diagonalDebtCoordinate_re_hasSum_windowLimit_source
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
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsumRe_of_diagonalDebtCoordinate_re_hasSum_source_primitive
      f C Creflect hhasSum hhasSumReflect
  let howner :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  tendsto_nhds_unique hcoordinate howner

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give convergence of
positive prime-defect real windows to the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_of_diagonalDebtCoordinate_re_hasSum_source_primitive
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
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
    f C Creflect hhasSum hhasSumReflect

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
