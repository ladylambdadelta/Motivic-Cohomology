import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicPayload.Owner

/-!
# Motive-root pullback-pushforward square payload rectangle lists

This file mirrors the public four-corner imported-rectangle list formulas for
the compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root northwest imported-rectangle list wrapper. -/
theorem TraceAnalyticMotive.publicNorthwestImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        probe =
      source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicNorthwestImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Motive-root northeast imported-rectangle list wrapper. -/
theorem TraceAnalyticMotive.publicNortheastImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        probe =
      target.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicNortheastImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Motive-root southwest imported-rectangle list wrapper. -/
theorem TraceAnalyticMotive.publicSouthwestImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        probe =
      source.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicSouthwestImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Motive-root southeast imported-rectangle list wrapper. -/
theorem TraceAnalyticMotive.publicSoutheastImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        probe =
      target.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicSoutheastImportedRectangles_eq_certificateLedgers
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
