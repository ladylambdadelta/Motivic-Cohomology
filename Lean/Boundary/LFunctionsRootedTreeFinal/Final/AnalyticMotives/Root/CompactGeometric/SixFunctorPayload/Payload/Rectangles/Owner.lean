import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Payload.Rectangles.Owner

/-!
# Top-root pullback-pushforward square payload rectangle lists

This file mirrors the motive-root four-corner imported-rectangle list formulas
under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root northwest imported-rectangle list wrapper. -/
theorem AnalyticMotivesRoot.publicNorthwestImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        probe =
      source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicNorthwestImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Top-root northeast imported-rectangle list wrapper. -/
theorem AnalyticMotivesRoot.publicNortheastImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        probe =
      target.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicNortheastImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Top-root southwest imported-rectangle list wrapper. -/
theorem AnalyticMotivesRoot.publicSouthwestImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        probe =
      source.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicSouthwestImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Top-root southeast imported-rectangle list wrapper. -/
theorem AnalyticMotivesRoot.publicSoutheastImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        probe =
      target.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicSoutheastImportedRectangles_eq_certificateLedgers
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
