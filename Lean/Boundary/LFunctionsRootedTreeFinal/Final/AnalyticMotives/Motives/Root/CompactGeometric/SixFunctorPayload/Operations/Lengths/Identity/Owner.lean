import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Identity.Horizontal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Identity.Vertical.Owner

/-!
# Motive-root identity pullback-pushforward operation lengths

This file collects motive-root horizontal- and vertical-identity
count-as-list-length facades for compact pullback-pushforward square payloads.
The aggregate surface exposes the northwest formulas matching the identity
operation payload aggregate.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root aggregate horizontal-identity northwest rectangle count-as-length. -/
theorem TraceAnalyticMotive.publicIdentity_northwestHorizontalCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityHorizontal_northwestCertificateLedgerRectangles_length
    generator
    probe

/-- Motive-root aggregate vertical-identity northwest rectangle count-as-length. -/
theorem TraceAnalyticMotive.publicIdentity_northwestVerticalCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityVertical_northwestCertificateLedgerRectangles_length
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
