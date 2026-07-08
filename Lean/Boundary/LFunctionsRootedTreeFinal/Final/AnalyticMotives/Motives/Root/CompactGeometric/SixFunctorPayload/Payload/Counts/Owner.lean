import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicPayload.Owner

/-!
# Motive-root pullback-pushforward square payload counts

This file mirrors the public four-corner imported-rectangle count formulas for
the compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root northwest imported-rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicNorthwestImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        probe =
      source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicNorthwestImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root northeast imported-rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicNortheastImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        probe =
      target.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicNortheastImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root southwest imported-rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicSouthwestImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        probe =
      source.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicSouthwestImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root southeast imported-rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicSoutheastImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        probe =
      target.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicSoutheastImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
