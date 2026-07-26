import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompression
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.FiberDomination

/-!
# Endpoint archimedean/correction residual source

This file owns the endpoint physical-absorption input which says that the
centered archimedean and correction packets dominate the endpoint fibers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Source endpoint trace-fiber domination by the centered archimedean and
correction packet Grams, after projection-complement nonnegativity has been
supplied. -/
theorem completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_source_owner_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
  fun hcomplement =>
    completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_source_primitive_of_projectionComplement
      f hcomplement

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
