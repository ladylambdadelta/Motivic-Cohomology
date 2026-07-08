import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicPayload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.Payload.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.Payload.TraceCalculus.Owner

/-!
# Base payload wrappers for six-functor interactions

This file exposes the base four-corner pullback-pushforward payload formulas at
the interaction namespace for imported rectangles.  Count-as-list-length
certification lives in the `Lengths` child, and trace-bookkeeping/rewrite-step
counts live in the `TraceCalculus` child; both are re-exported here.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback-pushforward northwest rectangle count is counted by source and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northwestImportedRectangleCount
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

/-- Pullback-pushforward northeast rectangle count is counted by target and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northeastImportedRectangleCount
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

/-- Pullback-pushforward southwest rectangle count is counted by source and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southwestImportedRectangleCount
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

/-- Pullback-pushforward southeast rectangle count is counted by target and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southeastImportedRectangleCount
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

/-- Pullback-pushforward northwest rectangle list is the source list followed by probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northwestImportedRectangles
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

/-- Pullback-pushforward northeast rectangle list is the target list followed by probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northeastImportedRectangles
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

/-- Pullback-pushforward southwest rectangle list is the source list followed by probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southwestImportedRectangles
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

/-- Pullback-pushforward southeast rectangle list is the target list followed by probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southeastImportedRectangles
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
