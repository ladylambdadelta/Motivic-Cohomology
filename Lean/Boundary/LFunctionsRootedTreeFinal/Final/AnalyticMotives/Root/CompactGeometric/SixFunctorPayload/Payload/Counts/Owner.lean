import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Payload.Counts.Owner

/-!
# Top-root pullback-pushforward square payload counts

This file mirrors the motive-root four-corner imported-rectangle count formulas
under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root northwest imported-rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicNorthwestImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        probe =
      source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicNorthwestImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root northeast imported-rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicNortheastImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        probe =
      target.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicNortheastImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root southwest imported-rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicSouthwestImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        probe =
      source.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicSouthwestImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root southeast imported-rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicSoutheastImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        probe =
      target.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicSoutheastImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
