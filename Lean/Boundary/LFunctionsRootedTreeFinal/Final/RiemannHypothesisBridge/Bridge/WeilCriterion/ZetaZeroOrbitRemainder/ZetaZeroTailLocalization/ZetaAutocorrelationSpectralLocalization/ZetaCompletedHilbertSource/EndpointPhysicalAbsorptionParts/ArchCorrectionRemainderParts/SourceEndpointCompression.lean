import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.SourceEndpointKernelSplit

/-!
# Source endpoint compression positivity

This file owns positivity of the canonical Hilbert-source endpoint compression
remainder.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Finite-Bessel nonnegativity of the canonical Hilbert-source endpoint
compression remainder after physical-boundary-to-ordered-heart transport. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_source_primitive_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    0 ≤
      completedBoundaryHilbertSourceEndpointCompressionRemainder
        (completedBoundaryHilbertSource f) :=
    completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointKernelSplitProp
      (completedBoundaryHilbertSource f)
      (completedBoundaryHilbertSourceEndpointKernelSplit_source_primitive_of_finiteBessel
        f D hnonPrime boundary_eq_ordered)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
