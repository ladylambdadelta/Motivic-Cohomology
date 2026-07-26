import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceTransportParts.DiagonalOwnerLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalOwnerLimitConditionalSource

/-!
# Conditional completed prime diagonal owner-window limit

This file exposes trace-transport diagonal owner limits from explicit
completed diagonal-debt real-coordinate `HasSum` inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give convergence of
finite diagonal-debt real windows to the owner diagonal-debt scalar at the
trace-transport layer. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_limit_core
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
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_primitive
    f C Creflect hhasSum hhasSumReflect

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
