import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalCoordinateTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalOwnerLimitConditionalSource

/-!
# Conditional diagonal coordinate transport source

This file isolates the explicit `HasSum` compatibility layer for transporting
the diagonal-debt coordinate presentation to the owner diagonal-debt scalar.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs transport the raw
diagonal-debt coordinate presentation to the owner completed diagonal-debt
scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_primitive
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
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝
          (Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_diagonalDebtCoordinate_re_hasSum_source_primitive
      f C Creflect hhasSum hhasSumReflect
  let howner :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_primitive
      f C Creflect hhasSum hhasSumReflect
  tendsto_nhds_unique hcoordinate howner

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
