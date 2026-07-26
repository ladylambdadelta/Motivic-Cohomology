import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceBessel

/-!
# Endpoint trace-compression source

This file owns the source trace-compression theorem for the completed endpoint
fiber.  The theorem is stated at the GNS/trace level, before any centered
archimedean/correction specialization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Finite-Bessel source nonnegativity of the canonical Hilbert-source
endpoint compression remainder.

This is the finite endpoint compression theorem for the canonical completed
Hilbert source.  It is the correct owner-level sink for endpoint reconstruction:
the endpoint fiber is controlled by the full positive trace state, not by a
single centered coordinate. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_traceCompression_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    0 ≤
      completedBoundaryHilbertSourceEndpointCompressionRemainder
        (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_source_of_finiteBessel
    f D hnonPrime boundary_eq_ordered

/-- Finite-Bessel source domination of the canonical endpoint trace fiber by
the completed ordered-heart scalar. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_traceCompression_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_compressionRemainder_nonnegative
    (completedBoundaryHilbertSource f)
    (completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_traceCompression_of_finiteBessel
      f D hnonPrime boundary_eq_ordered)

/-- Finite-Bessel source endpoint trace-compression domination by the positive
completed GNS presentation. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_traceCompression_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  completedEndpointTraceFiber_gram_le_positivePresentation_of_finiteBessel
    f D hnonPrime boundary_eq_positive

/-- Finite-Bessel source nonnegativity of the seed positive-presentation
endpoint compression remainder. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_traceCompression_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  completedEndpointFiberPositivePresentationRemainder_nonnegative_of_finiteBessel
    f D hnonPrime boundary_eq_positive

/-- Finite-Bessel source endpoint-kernel split for the canonical completed
Hilbert source. -/
theorem completedBoundaryHilbertSourceEndpointKernelSplit_traceCompression_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    completedBoundaryHilbertSourceEndpointKernelSplit
      (completedBoundaryHilbertSource f) :=
  let source : CompletedBoundaryHilbertSource :=
    completedBoundaryHilbertSource f
  let kernelRemainder : ℝ :=
    completedBoundaryHilbertSourceEndpointCompressionRemainder source
  let hkernel : 0 ≤ kernelRemainder :=
    completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_traceCompression_of_finiteBessel
      f D hnonPrime boundary_eq_ordered
  let hordered :
      completedOrderedHeartScalar source =
        (completedBoundaryHilbertSourceEndpointTraceFiber source).gram +
          kernelRemainder :=
    endpointTraceDebt_add_sub_cancel
      (completedOrderedHeartScalar source)
      (completedBoundaryHilbertSourceEndpointTraceFiber source).gram
  Exists.intro kernelRemainder (And.intro hordered hkernel)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
