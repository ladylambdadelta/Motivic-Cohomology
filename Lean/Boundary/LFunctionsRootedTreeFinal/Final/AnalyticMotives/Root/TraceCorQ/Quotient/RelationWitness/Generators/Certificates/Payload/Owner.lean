import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.Certificates.Payload.Owner

/-!
# Top-root generated support-witness certificate payloads

This file exposes the imported-rectangle, certificate-ledger, bookkeeping, and
rewrite-step payload facts for the canonical support witness attached to a
single relation generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes support-witness imported counts by singleton ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_importedRectangleCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationLedger.singleton relation).importedRectangleCount :=
  TraceCorQ.relationGenerator_supportWitness_importedRectangleCount_eq_ledger
    relation

/-- The top root exposes support-witness imported rectangles by singleton ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_importedRectangles_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangles =
      (TraceCorQRelationLedger.singleton relation).importedRectangles :=
  TraceCorQ.relationGenerator_supportWitness_importedRectangles_eq_ledger
    relation

/-- The top root exposes support-witness certificate ledgers by singleton ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_certificateLedger_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_ledger
    relation

/-- The top root exposes support-witness bookkeeping counts by singleton ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_traceBookkeepingCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).traceBookkeepingCount =
      (TraceCorQRelationLedger.singleton relation).traceBookkeepingCount :=
  TraceCorQ.relationGenerator_supportWitness_traceBookkeepingCount_eq_ledger
    relation

/-- The top root exposes support-witness rewrite-step counts by singleton ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_rewriteStepCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      (TraceCorQRelationLedger.singleton relation).rewriteStepCount :=
  TraceCorQ.relationGenerator_supportWitness_rewriteStepCount_eq_ledger
    relation

/-- The top root exposes support-witness imported counts by generator. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_importedRectangleCount_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      relation.importedRectangleCount + 0 :=
  TraceCorQ.relationGenerator_supportWitness_importedRectangleCount_eq_generator
    relation

/-- The top root exposes support-witness imported rectangles by generator. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_importedRectangles_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangles =
      relation.importedRectangles ++ [] :=
  TraceCorQ.relationGenerator_supportWitness_importedRectangles_eq_generator
    relation

/-- The top root exposes support-witness certificate ledgers by generator. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_certificateLedger_eq_generator_payload
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_generator_payload
    relation

/-- The top root exposes support-witness bookkeeping counts by generator. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_traceBookkeepingCount_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).traceBookkeepingCount =
      relation.traceBookkeepingCount + 0 :=
  TraceCorQ.relationGenerator_supportWitness_traceBookkeepingCount_eq_generator
    relation

/-- The top root exposes support-witness rewrite-step counts by generator. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_rewriteStepCount_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      relation.rewriteStepCount + 0 :=
  TraceCorQ.relationGenerator_supportWitness_rewriteStepCount_eq_generator
    relation

/-- The top root exposes support-witness imported counts by certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_importedRectangleCount_eq_certificateLedger_count
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.importedRectangleCount :=
  TraceCorQ.relationGenerator_supportWitness_importedRectangleCount_eq_certificateLedger_count
    relation

/-- The top root exposes support-witness imported rectangles by certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_importedRectangles_eq_certificateLedger_rectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangles =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.importedRectangles :=
  TraceCorQ.relationGenerator_supportWitness_importedRectangles_eq_certificateLedger_rectangles
    relation

/-- The top root exposes support-witness imported count-as-length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_importedRectangleCount_eq_length_importedRectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportWitness relation).importedRectangles.length :=
  TraceCorQ.relationGenerator_supportWitness_importedRectangleCount_eq_length_importedRectangles
    relation

/-- The top root exposes support-witness bookkeeping counts by certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_traceBookkeepingCount_eq_certificateLedger_count
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).traceBookkeepingCount =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.traceBookkeepingCount :=
  TraceCorQ.relationGenerator_supportWitness_traceBookkeepingCount_eq_certificateLedger_count
    relation

/-- The top root exposes support-witness rewrite-step counts by certificate ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_rewriteStepCount_eq_certificateLedger_count
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.rewriteStepCount :=
  TraceCorQ.relationGenerator_supportWitness_rewriteStepCount_eq_certificateLedger_count
    relation

end AnalyticMotives
end LFunctions
end Boundary
