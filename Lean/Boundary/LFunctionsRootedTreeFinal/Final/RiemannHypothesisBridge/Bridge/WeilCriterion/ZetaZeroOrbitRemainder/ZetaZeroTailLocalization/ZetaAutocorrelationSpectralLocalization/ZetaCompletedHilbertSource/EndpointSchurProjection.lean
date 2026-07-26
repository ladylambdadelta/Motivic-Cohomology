import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompression
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.SourceEndpointSchurProjection

/-!
# Endpoint Schur projection

This file owns the finite endpoint Schur/projection theorem for completed
Hilbert sources.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Source Schur/projection nonnegativity of the canonical endpoint compression
remainder in the positive GNS presentation, after projection-complement
nonnegativity has been supplied. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  fun hcomplement =>
    completedEndpointFiberPositivePresentationRemainder_nonnegative_of_archCorrectionRemainder
      f
      (completedEndpointFiberArchCorrectionRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
        f hcomplement)

/-- Source Schur/projection domination of the two endpoint trace fibers for a
canonical completed Hilbert source after projection-complement nonnegativity has
been supplied. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_sourceSchurProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  fun hcomplement =>
    endpointFiberGram_le_positivePresentation_of_positivePresentationRemainder_nonnegative
      f
      (completedEndpointFiberPositivePresentationRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
        f hcomplement)

/-- Owner endpoint-kernel split for a canonical completed Hilbert source, after
projection-complement nonnegativity has been supplied. -/
theorem completedBoundaryHilbertSourceEndpointKernelSplit_sourceSchurProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    completedBoundaryHilbertSourceEndpointKernelSplit
      (completedBoundaryHilbertSource f) :=
  fun hcomplement =>
  let source : CompletedBoundaryHilbertSource :=
    completedBoundaryHilbertSource f
  let kernelRemainder : ℝ :=
    completedBoundaryHilbertSourceEndpointCompressionRemainder source
  let hpositive :
      0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
    completedEndpointFiberPositivePresentationRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
      f hcomplement
  let hkernel :
      0 ≤ kernelRemainder :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedEndpointFiberPositivePresentationRemainder_eq_sourceEndpointCompressionRemainder
        f)
      hpositive
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
