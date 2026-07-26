import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompressionSource

/-!
# Endpoint positive-presentation remainder source

This file owns positivity of the endpoint compression remainder after the
finite endpoint trace fiber has been removed from the positive GNS
presentation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Finite-Bessel nonnegativity of the endpoint positive-presentation
compression remainder after physical-boundary-to-positive-presentation
transport. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_source_primitive_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  completedEndpointFiberPositivePresentationRemainder_nonnegative_traceCompression_of_finiteBessel
    f D hnonPrime boundary_eq_positive

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
