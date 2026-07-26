import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ContourTomography
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryCancellationRealShadowParts.TwoFaceWindowParts.ContourCancellation

/-!
# Boundary cancellation two-face window source

This file owns the rectangular two-face cancellation input for the completed
prime-power autocorrelation stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators Topology

namespace ZetaAdmissibleFunction

/-- Source rectangular cancellation for the paired completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_core_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_primitive
      f hmajorant

/-- Source ledger cancellation for the paired completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceKernel_source_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_core_owner
      f hmajorant

/-- Source rectangular cancellation for the paired completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceKernel_source_owner
      f hmajorant

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
