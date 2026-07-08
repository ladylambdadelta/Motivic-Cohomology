import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Identity.Horizontal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Identity.Vertical.Owner

/-!
# Motive-root identity pullback-pushforward operation payload

This file collects motive-root identity-operation payload facades for the
compact pullback-pushforward square.  The aggregate surface exposes the
northwest rectangle-count formulas for horizontal and vertical identities.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root aggregate horizontal-identity northwest rectangle count. -/
theorem TraceAnalyticMotive.publicIdentity_northwestHorizontalImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_northwestImportedRectangleCount
    generator
    probe

/-- Motive-root aggregate vertical-identity northwest rectangle count. -/
theorem TraceAnalyticMotive.publicIdentity_northwestVerticalImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityVertical_northwestImportedRectangleCount
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
