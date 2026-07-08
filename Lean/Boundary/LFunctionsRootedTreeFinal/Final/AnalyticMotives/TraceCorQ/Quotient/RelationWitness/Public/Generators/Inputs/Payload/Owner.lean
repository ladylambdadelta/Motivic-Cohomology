import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Inputs.Payload.Owner

/-!
# Public generated support-input payloads

This file exposes the certificate and analytic payload projections of the
support quotient input attached to a relation generator under the `TraceCorQ`
aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes generated support-input formal sums. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_formalSum_eq_support
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).formalSum =
      relation.support :=
  TraceCorQRelationGenerator.supportQuotientInput_formalSum_eq_support
    relation

/-- The trace-correspondence root exposes generated support-input singleton ledgers. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_ledger_eq_singleton
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).ledger =
      TraceCorQRelationLedger.singleton relation :=
  TraceCorQRelationGenerator.supportQuotientInput_ledger_eq_singleton
    relation

/-- The trace-correspondence root exposes generated support-input certificate splits by ledger. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_certificateLedger_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.support.certificateLedger
        (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  TraceCorQRelationGenerator.supportQuotientInput_certificateLedger_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-input imported counts by ledger. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_importedRectangleCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangleCount =
      relation.support.importedRectangleCount +
        (TraceCorQRelationLedger.singleton relation).importedRectangleCount :=
  TraceCorQRelationGenerator.supportQuotientInput_importedRectangleCount_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-input imported rectangles by ledger. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_importedRectangles_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangles =
      relation.support.importedRectangles ++
        (TraceCorQRelationLedger.singleton relation).importedRectangles :=
  TraceCorQRelationGenerator.supportQuotientInput_importedRectangles_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-input bookkeeping counts by ledger. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_traceBookkeepingCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).traceBookkeepingCount =
      relation.support.traceBookkeepingCount +
        (TraceCorQRelationLedger.singleton relation).traceBookkeepingCount :=
  TraceCorQRelationGenerator.supportQuotientInput_traceBookkeepingCount_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-input rewrite-step counts by ledger. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_rewriteStepCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).rewriteStepCount =
      relation.support.rewriteStepCount +
        (TraceCorQRelationLedger.singleton relation).rewriteStepCount :=
  TraceCorQRelationGenerator.supportQuotientInput_rewriteStepCount_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-input count-as-length. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_importedRectangleCount_eq_length_importedRectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangles.length :=
  TraceCorQRelationGenerator.supportQuotientInput_importedRectangleCount_eq_length_importedRectangles
    relation

/-- The trace-correspondence root exposes generated support-input certificate splits by generator. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_certificateLedger_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.support.certificateLedger
        (ResidueChannelCertificateLedger.append
          relation.certificateLedger
          ResidueChannelCertificateLedger.empty) :=
  TraceCorQRelationGenerator.supportQuotientInput_certificateLedger_eq_support_generator
    relation

/-- The trace-correspondence root exposes generated support-input imported counts by generator. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_importedRectangleCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangleCount =
      relation.support.importedRectangleCount +
        (relation.importedRectangleCount + 0) :=
  TraceCorQRelationGenerator.supportQuotientInput_importedRectangleCount_eq_support_generator
    relation

/-- The trace-correspondence root exposes generated support-input imported rectangles by generator. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_importedRectangles_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangles =
      relation.support.importedRectangles ++
        (relation.importedRectangles ++ []) :=
  TraceCorQRelationGenerator.supportQuotientInput_importedRectangles_eq_support_generator
    relation

/-- The trace-correspondence root exposes generated support-input bookkeeping counts by generator. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_traceBookkeepingCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).traceBookkeepingCount =
      relation.support.traceBookkeepingCount +
        (relation.traceBookkeepingCount + 0) :=
  TraceCorQRelationGenerator.supportQuotientInput_traceBookkeepingCount_eq_support_generator
    relation

/-- The trace-correspondence root exposes generated support-input rewrite-step counts by generator. -/
theorem TraceCorQ.relationGenerator_supportQuotientInput_rewriteStepCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).rewriteStepCount =
      relation.support.rewriteStepCount +
        (relation.rewriteStepCount + 0) :=
  TraceCorQRelationGenerator.supportQuotientInput_rewriteStepCount_eq_support_generator
    relation

end AnalyticMotives
end LFunctions
end Boundary
