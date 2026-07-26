import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.PositivePresentationRemainder

/-!
# Endpoint positive-presentation domination source

This file owns domination of the finite endpoint trace fiber by the completed
positive GNS presentation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Finite-Bessel endpoint trace domination by the positive GNS presentation
after physical-boundary-to-positive-presentation transport. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_source_primitive_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  endpointFiberGram_le_positivePresentation_of_positivePresentationRemainder_nonnegative
    f
    (completedEndpointFiberPositivePresentationRemainder_nonnegative_source_primitive_of_finiteBessel
      f D hnonPrime boundary_eq_positive)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
