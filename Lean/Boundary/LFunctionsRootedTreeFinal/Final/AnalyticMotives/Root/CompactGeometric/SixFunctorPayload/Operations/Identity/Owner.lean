import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorPayload.Operations.Identity.Horizontal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorPayload.Operations.Identity.Vertical.Owner

/-!
# Top-root identity pullback-pushforward operation payload

This file collects top-root identity-operation payload facades for the compact
pullback-pushforward square.  The aggregate surface exposes the northwest
rectangle-count formulas for horizontal and vertical identities.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root aggregate horizontal-identity northwest rectangle count. -/
theorem AnalyticMotivesRoot.publicIdentity_northwestHorizontalImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentity_northwestHorizontalImportedRectangleCount
    generator
    probe

/-- Top-root aggregate vertical-identity northwest rectangle count. -/
theorem AnalyticMotivesRoot.publicIdentity_northwestVerticalImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentity_northwestVerticalImportedRectangleCount
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
