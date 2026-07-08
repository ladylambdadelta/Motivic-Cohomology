import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.Owner

/-!
# Top-root trace-correspondence relation ledgers

This file exposes finite relation-ledger bookkeeping for Q-linear trace
correspondences under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes empty-left append for relation ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_empty_append
    (ledger : TraceCorQRelationLedger) :
    TraceCorQRelationLedger.append
      TraceCorQRelationLedger.empty
      ledger =
      ledger :=
  TraceCorQRelationLedger.empty_append
    ledger

/-- The top root exposes empty-right append for relation ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_append_empty
    (ledger : TraceCorQRelationLedger) :
    TraceCorQRelationLedger.append
      ledger
      TraceCorQRelationLedger.empty =
      ledger :=
  TraceCorQRelationLedger.append_empty
    ledger

/-- The top root exposes relation-ledger append associativity. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_append_assoc
    (first second third : TraceCorQRelationLedger) :
    TraceCorQRelationLedger.append
      (TraceCorQRelationLedger.append first second)
      third =
      TraceCorQRelationLedger.append
        first
        (TraceCorQRelationLedger.append second third) :=
  TraceCorQRelationLedger.append_assoc
    first
    second
    third

/-- The top root exposes the empty relation-ledger certificate. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_empty_certificateLedger :
    TraceCorQRelationLedger.empty.certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationLedger.empty_certificateLedger

/-- The top root exposes singleton relation-ledger certificates. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_singleton_certificateLedger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationLedger.singleton relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationLedger.singleton_certificateLedger
    relation

/-- The top root exposes relation-ledger certificate compatibility with append. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_append_certificateLedger
    (first second : TraceCorQRelationLedger) :
    (TraceCorQRelationLedger.append first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.certificateLedger
        second.certificateLedger :=
  TraceCorQRelationLedger.append_certificateLedger
    first
    second

/-- The top root exposes empty relation-ledger imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_empty_importedRectangleCount :
    TraceCorQRelationLedger.empty.importedRectangleCount =
      0 :=
  TraceCorQRelationLedger.empty_importedRectangleCount

/-- The top root exposes singleton relation-ledger imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_singleton_importedRectangleCount
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationLedger.singleton relation).importedRectangleCount =
      relation.importedRectangleCount +
        0 :=
  TraceCorQRelationLedger.singleton_importedRectangleCount
    relation

/-- The top root exposes imported-rectangle count additivity under ledger append. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_append_importedRectangleCount
    (first second : TraceCorQRelationLedger) :
    (TraceCorQRelationLedger.append first second).importedRectangleCount =
      first.importedRectangleCount +
        second.importedRectangleCount :=
  TraceCorQRelationLedger.append_importedRectangleCount
    first
    second

/-- The top root exposes empty relation-ledger imported-rectangle lists. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_empty_importedRectangles :
    TraceCorQRelationLedger.empty.importedRectangles =
      [] :=
  TraceCorQRelationLedger.empty_importedRectangles

/-- The top root exposes singleton relation-ledger imported-rectangle lists. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_singleton_importedRectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationLedger.singleton relation).importedRectangles =
      relation.importedRectangles ++
        [] :=
  TraceCorQRelationLedger.singleton_importedRectangles
    relation

/-- The top root exposes imported-rectangle list concatenation under ledger append. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_append_importedRectangles
    (first second : TraceCorQRelationLedger) :
    (TraceCorQRelationLedger.append first second).importedRectangles =
      first.importedRectangles ++
        second.importedRectangles :=
  TraceCorQRelationLedger.append_importedRectangles
    first
    second

/-- The top root exposes relation-ledger imported-rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_importedRectangleCount_eq_length
    (ledger : TraceCorQRelationLedger) :
    ledger.importedRectangleCount =
      ledger.importedRectangles.length :=
  TraceCorQRelationLedger.importedRectangleCount_eq_length_importedRectangles
    ledger

/-- The top root exposes empty relation-ledger trace-bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_empty_traceBookkeepingCount :
    TraceCorQRelationLedger.empty.traceBookkeepingCount =
      0 :=
  TraceCorQRelationLedger.empty_traceBookkeepingCount

/-- The top root exposes singleton relation-ledger trace-bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_singleton_traceBookkeepingCount
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationLedger.singleton relation).traceBookkeepingCount =
      relation.traceBookkeepingCount +
        0 :=
  TraceCorQRelationLedger.singleton_traceBookkeepingCount
    relation

/-- The top root exposes trace-bookkeeping count additivity under ledger append. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_append_traceBookkeepingCount
    (first second : TraceCorQRelationLedger) :
    (TraceCorQRelationLedger.append first second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  TraceCorQRelationLedger.append_traceBookkeepingCount
    first
    second

/-- The top root exposes empty relation-ledger rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_empty_rewriteStepCount :
    TraceCorQRelationLedger.empty.rewriteStepCount =
      0 :=
  TraceCorQRelationLedger.empty_rewriteStepCount

/-- The top root exposes singleton relation-ledger rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_singleton_rewriteStepCount
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationLedger.singleton relation).rewriteStepCount =
      relation.rewriteStepCount +
        0 :=
  TraceCorQRelationLedger.singleton_rewriteStepCount
    relation

/-- The top root exposes rewrite-step count additivity under ledger append. -/
theorem AnalyticMotivesRoot.traceCorQRelationLedger_append_rewriteStepCount
    (first second : TraceCorQRelationLedger) :
    (TraceCorQRelationLedger.append first second).rewriteStepCount =
      first.rewriteStepCount +
        second.rewriteStepCount :=
  TraceCorQRelationLedger.append_rewriteStepCount
    first
    second

end AnalyticMotives
end LFunctions
end Boundary
