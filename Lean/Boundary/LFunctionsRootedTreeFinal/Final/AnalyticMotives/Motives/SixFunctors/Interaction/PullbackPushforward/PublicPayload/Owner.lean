import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Lists.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicPayload.Lengths.Owner

/-!
# Public payload wrappers for the pullback-pushforward square

This file exposes compact public names for the imported finite-rectangle and
trace-calculus payload carried by the four corners of the compact
pullback-pushforward square.  Count-as-list-length wrappers live in the
`Lengths` child and are re-exported by this public payload root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Northwest corner imported-rectangle count is counted by source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicNorthwestImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        probe =
      source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Northeast corner imported-rectangle count is counted by target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicNortheastImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        probe =
      target.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Southwest corner imported-rectangle count is counted by source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicSouthwestImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        probe =
      source.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Southeast corner imported-rectangle count is counted by target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicSoutheastImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        probe =
      target.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Northwest corner rectangle list is source ledger list followed by probe-target ledger list. -/
theorem TraceSixFunctorPullbackPushforward.publicNorthwestImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        probe =
      source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.northwestImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Northeast corner rectangle list is target ledger list followed by probe-target ledger list. -/
theorem TraceSixFunctorPullbackPushforward.publicNortheastImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        probe =
      target.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.northeastImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Southwest corner rectangle list is source ledger list followed by probe-source ledger list. -/
theorem TraceSixFunctorPullbackPushforward.publicSouthwestImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        probe =
      source.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.southwestImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Southeast corner rectangle list is target ledger list followed by probe-source ledger list. -/
theorem TraceSixFunctorPullbackPushforward.publicSoutheastImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        probe =
      target.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.southeastImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Northwest corner bookkeeping count is counted by source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicNorthwestTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        probe =
      source.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Northeast corner bookkeeping count is counted by target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicNortheastTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        probe =
      target.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Southwest corner bookkeeping count is counted by source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicSouthwestTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        probe =
      source.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Southeast corner bookkeeping count is counted by target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicSoutheastTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        probe =
      target.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Northwest corner rewrite-step count is counted by source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicNorthwestRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        probe =
      source.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.northwestRewriteStepCount_eq_certificateLedgers
    morphism
    probe

/-- Northeast corner rewrite-step count is counted by target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicNortheastRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        probe =
      target.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.northeastRewriteStepCount_eq_certificateLedgers
    morphism
    probe

/-- Southwest corner rewrite-step count is counted by source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicSouthwestRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        probe =
      source.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.southwestRewriteStepCount_eq_certificateLedgers
    morphism
    probe

/-- Southeast corner rewrite-step count is counted by target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicSoutheastRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        probe =
      target.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.southeastRewriteStepCount_eq_certificateLedgers
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
