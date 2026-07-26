import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompressionSource

/-!
# Source endpoint kernel split

This file owns the canonical endpoint-kernel split for the completed Hilbert
source.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Finite-Bessel endpoint kernel split for the canonical completed Hilbert
source after physical-boundary-to-ordered-heart transport. -/
theorem completedBoundaryHilbertSourceEndpointKernelSplit_source_primitive_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    completedBoundaryHilbertSourceEndpointKernelSplit
      (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointKernelSplit_traceCompression_of_finiteBessel
    f D hnonPrime boundary_eq_ordered

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
