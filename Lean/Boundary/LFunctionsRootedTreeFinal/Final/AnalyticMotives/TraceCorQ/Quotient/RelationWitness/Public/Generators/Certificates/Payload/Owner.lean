import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Payload.Owner

/-!
# Public generated support-witness payloads

This file exposes the certificate and analytic payload projections of the
canonical relation witness attached to a relation generator under the
`TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes support-witness imported counts by ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_importedRectangleCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationLedger.singleton relation).importedRectangleCount :=
  TraceCorQRelationGenerator.supportWitness_importedRectangleCount_eq_ledger
    relation

/-- The trace-correspondence root exposes support-witness imported rectangles by ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_importedRectangles_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangles =
      (TraceCorQRelationLedger.singleton relation).importedRectangles :=
  TraceCorQRelationGenerator.supportWitness_importedRectangles_eq_ledger
    relation

/-- The trace-correspondence root exposes support-witness certificate ledgers by ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_ledger
    relation

/-- The trace-correspondence root exposes support-witness bookkeeping counts by ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_traceBookkeepingCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).traceBookkeepingCount =
      (TraceCorQRelationLedger.singleton relation).traceBookkeepingCount :=
  TraceCorQRelationGenerator.supportWitness_traceBookkeepingCount_eq_ledger
    relation

/-- The trace-correspondence root exposes support-witness rewrite-step counts by ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_rewriteStepCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      (TraceCorQRelationLedger.singleton relation).rewriteStepCount :=
  TraceCorQRelationGenerator.supportWitness_rewriteStepCount_eq_ledger
    relation

/-- The trace-correspondence root exposes support-witness imported counts by generator. -/
theorem TraceCorQ.relationGenerator_supportWitness_importedRectangleCount_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      relation.importedRectangleCount + 0 :=
  TraceCorQRelationGenerator.supportWitness_importedRectangleCount_eq_generator
    relation

/-- The trace-correspondence root exposes support-witness imported rectangles by generator. -/
theorem TraceCorQ.relationGenerator_supportWitness_importedRectangles_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangles =
      relation.importedRectangles ++ [] :=
  TraceCorQRelationGenerator.supportWitness_importedRectangles_eq_generator
    relation

/-- The trace-correspondence root exposes support-witness certificate ledgers by generator. -/
theorem TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_generator_payload
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator_payload
    relation

/-- The trace-correspondence root exposes support-witness bookkeeping counts by generator. -/
theorem TraceCorQ.relationGenerator_supportWitness_traceBookkeepingCount_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).traceBookkeepingCount =
      relation.traceBookkeepingCount + 0 :=
  TraceCorQRelationGenerator.supportWitness_traceBookkeepingCount_eq_generator
    relation

/-- The trace-correspondence root exposes support-witness rewrite-step counts by generator. -/
theorem TraceCorQ.relationGenerator_supportWitness_rewriteStepCount_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      relation.rewriteStepCount + 0 :=
  TraceCorQRelationGenerator.supportWitness_rewriteStepCount_eq_generator
    relation

/-- The trace-correspondence root exposes support-witness imported counts by certificate ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_importedRectangleCount_eq_certificateLedger_count
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.importedRectangleCount :=
  TraceCorQRelationGenerator.supportWitness_importedRectangleCount_eq_certificateLedger_count
    relation

/-- The trace-correspondence root exposes support-witness imported rectangles by certificate ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_importedRectangles_eq_certificateLedger_rectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangles =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.importedRectangles :=
  TraceCorQRelationGenerator.supportWitness_importedRectangles_eq_certificateLedger_rectangles
    relation

/-- The trace-correspondence root exposes support-witness count-as-length. -/
theorem TraceCorQ.relationGenerator_supportWitness_importedRectangleCount_eq_length_importedRectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportWitness relation).importedRectangles.length :=
  TraceCorQRelationGenerator.supportWitness_importedRectangleCount_eq_length_importedRectangles
    relation

/-- The trace-correspondence root exposes support-witness bookkeeping counts by certificate ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_traceBookkeepingCount_eq_certificateLedger_count
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).traceBookkeepingCount =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.traceBookkeepingCount :=
  TraceCorQRelationGenerator.supportWitness_traceBookkeepingCount_eq_certificateLedger_count
    relation

/-- The trace-correspondence root exposes support-witness rewrite-step counts by certificate ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_rewriteStepCount_eq_certificateLedger_count
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.rewriteStepCount :=
  TraceCorQRelationGenerator.supportWitness_rewriteStepCount_eq_certificateLedger_count
    relation

end AnalyticMotives
end LFunctions
end Boundary
