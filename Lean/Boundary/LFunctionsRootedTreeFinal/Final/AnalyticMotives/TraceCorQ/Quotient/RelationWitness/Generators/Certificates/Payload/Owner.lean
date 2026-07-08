import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Payload.Owner

/-!
# Payload projections for generated relation witnesses

This file records the imported-rectangle, bookkeeping, and rewrite-step payload
carried by the canonical witness attached to a single relation generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The canonical support witness carries the singleton relation-ledger rectangle count. -/
theorem TraceCorQRelationGenerator.supportWitness_importedRectangleCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationLedger.singleton relation).importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.supportWitness relation)

/-- The canonical support witness exposes the singleton relation-ledger rectangle list. -/
theorem TraceCorQRelationGenerator.supportWitness_importedRectangles_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangles =
      (TraceCorQRelationLedger.singleton relation).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationGenerator.supportWitness relation)

/-- The canonical support witness carries the singleton relation-ledger certificate ledger. -/
theorem TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger relation

/-- The canonical support witness carries the singleton relation-ledger bookkeeping count. -/
theorem TraceCorQRelationGenerator.supportWitness_traceBookkeepingCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).traceBookkeepingCount =
      (TraceCorQRelationLedger.singleton relation).traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationGenerator.supportWitness relation)

/-- The canonical support witness carries the singleton relation-ledger rewrite-step count. -/
theorem TraceCorQRelationGenerator.supportWitness_rewriteStepCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      (TraceCorQRelationLedger.singleton relation).rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.supportWitness relation)

/-- The canonical support witness imports the relation generator rectangle count. -/
theorem TraceCorQRelationGenerator.supportWitness_importedRectangleCount_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      relation.importedRectangleCount + 0 :=
  Eq.trans
    (TraceCorQRelationGenerator.supportWitness_importedRectangleCount_eq_ledger
      relation)
    (TraceCorQRelationLedger.singleton_importedRectangleCount relation)

/-- The canonical support witness exposes the relation generator rectangle list. -/
theorem TraceCorQRelationGenerator.supportWitness_importedRectangles_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangles =
      relation.importedRectangles ++ [] :=
  Eq.trans
    (TraceCorQRelationGenerator.supportWitness_importedRectangles_eq_ledger
      relation)
    (TraceCorQRelationLedger.singleton_importedRectangles relation)

/-- The canonical support witness carries the relation generator certificate ledger. -/
theorem TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator_payload
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator
    relation

/-- The canonical support witness carries the relation generator bookkeeping count. -/
theorem TraceCorQRelationGenerator.supportWitness_traceBookkeepingCount_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).traceBookkeepingCount =
      relation.traceBookkeepingCount + 0 :=
  Eq.trans
    (TraceCorQRelationGenerator.supportWitness_traceBookkeepingCount_eq_ledger
      relation)
    (TraceCorQRelationLedger.singleton_traceBookkeepingCount relation)

/-- The canonical support witness carries the relation generator rewrite-step count. -/
theorem TraceCorQRelationGenerator.supportWitness_rewriteStepCount_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      relation.rewriteStepCount + 0 :=
  Eq.trans
    (TraceCorQRelationGenerator.supportWitness_rewriteStepCount_eq_ledger
      relation)
    (TraceCorQRelationLedger.singleton_rewriteStepCount relation)

/-- The canonical support witness count is counted by its certificate ledger. -/
theorem TraceCorQRelationGenerator.supportWitness_importedRectangleCount_eq_certificateLedger_count
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_certificateLedger_count
    (TraceCorQRelationGenerator.supportWitness relation)

/-- The canonical support witness rectangle list is extracted from its certificate ledger. -/
theorem TraceCorQRelationGenerator.supportWitness_importedRectangles_eq_certificateLedger_rectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangles =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_certificateLedger_rectangles
    (TraceCorQRelationGenerator.supportWitness relation)

/-- The canonical support witness count is the length of its imported rectangle list. -/
theorem TraceCorQRelationGenerator.supportWitness_importedRectangleCount_eq_length_importedRectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportWitness relation).importedRectangles.length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.supportWitness relation)

/-- The canonical support witness bookkeeping count is counted by its certificate ledger. -/
theorem TraceCorQRelationGenerator.supportWitness_traceBookkeepingCount_eq_certificateLedger_count
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).traceBookkeepingCount =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_certificateLedger_count
    (TraceCorQRelationGenerator.supportWitness relation)

/-- The canonical support witness rewrite-step count is counted by its certificate ledger. -/
theorem TraceCorQRelationGenerator.supportWitness_rewriteStepCount_eq_certificateLedger_count
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      (TraceCorQRelationGenerator.supportWitness relation).certificateLedger.rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_certificateLedger_count
    (TraceCorQRelationGenerator.supportWitness relation)

end AnalyticMotives
end LFunctions
end Boundary
