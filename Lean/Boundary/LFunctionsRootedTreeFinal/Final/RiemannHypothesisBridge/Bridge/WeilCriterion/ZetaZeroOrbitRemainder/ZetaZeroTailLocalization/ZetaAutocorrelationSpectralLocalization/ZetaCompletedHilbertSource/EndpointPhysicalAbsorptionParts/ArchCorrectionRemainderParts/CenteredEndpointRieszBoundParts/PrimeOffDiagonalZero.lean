import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointRieszBoundParts.PositiveBesselRemainder
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBesselParts.PrimeOffDiagonalWindow

/-!
# Centered endpoint Riesz prime off-diagonal zero source

This file owns the prime off-diagonal annihilation input consumed by the
centered endpoint Riesz source split.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Source annihilation of the completed prime off-diagonal channel for the
centered endpoint Riesz lane. -/
theorem completedPrimeOffDiagonalChannel_eq_zero_centeredRiesz_source
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    completedPrimeOffDiagonalChannel f = 0 :=
  completedPrimeOffDiagonalChannel_eq_zero_ownerTraceReconstruction f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
