import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointSchurProjection
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionSource

/-!
# Endpoint physical absorption

This file owns the physical endpoint-absorption positivity statement.  The
Hilbert-source kernel split consumes this theorem before any finite centered
archimedean/correction packet inequality is used.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Canonical-source endpoint Schur/projection domination transported to the
positive GNS presentation, after projection-complement nonnegativity has been
supplied. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_ownerSchurProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  fun hcomplement =>
    completedEndpointTraceFiber_gram_le_positivePresentation_sourceSchurProjection_of_projectionComplement
      f hcomplement

/-- Owner physical endpoint absorption as the boundary domination of endpoint
diagonal debt. -/
theorem completedEndpointDiagonalDebt_le_boundaryChannel_re_ownerPhysicalAbsorption
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    (zetaCompletedEndpointCorrectionPacket f).diagonalDebt ≤
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
  (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_iff_diagonalDebt_le_boundary
    f).mp
    (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_source
      f D hnonPrime)

/-- Owner physical endpoint absorption: after completing the endpoint square,
the remaining physical boundary scalar is nonnegative. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_owner
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_source f D hnonPrime

/-- Source physical endpoint absorption after supplying the non-prime residual
from the archimedean/correction owner theorem and projection-complement
nonnegativity. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_source_owner_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  fun hcomplement =>
  let harch :
      0 ≤ completedEndpointFiberArchCorrectionRemainder f :=
    completedEndpointFiberArchCorrectionRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
      f hcomplement
  let hnonPrime :
      CompletedEndpointNonPrimeTraceResidualNonnegative f :=
    completedEndpointNonPrimeTraceResidualNonnegative_of_archCorrectionRemainder_nonnegative
      f harch
  completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_source
    f D hnonPrime

/-- Source boundary domination of endpoint diagonal debt after the non-prime
residual has been supplied by the archimedean/correction owner theorem and
projection-complement nonnegativity. -/
theorem completedEndpointDiagonalDebt_le_boundaryChannel_re_source_ownerPhysicalAbsorption_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (zetaCompletedEndpointCorrectionPacket f).diagonalDebt ≤
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
  fun hcomplement =>
    (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_iff_diagonalDebt_le_boundary
      f).mp
      (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_source_owner_of_projectionComplement
        f D hcomplement)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
