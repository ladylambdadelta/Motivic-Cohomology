import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Candidates.Payload.Owner

/-!
# Public generated support-candidate payloads

This file exposes the certificate and analytic payload projections of the
support candidate attached to a relation generator under the `TraceCorQ`
aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes generated support-candidate formal sums. -/
theorem TraceCorQ.relationGenerator_supportCandidate_formalSum_eq_support
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).formalSum =
      relation.support :=
  TraceCorQRelationGenerator.supportCandidate_formalSum_eq_support
    relation

/-- The trace-correspondence root exposes generated support-candidate singleton ledgers. -/
theorem TraceCorQ.relationGenerator_supportCandidate_ledger_eq_singleton
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).ledger =
      TraceCorQRelationLedger.singleton relation :=
  TraceCorQRelationGenerator.supportCandidate_ledger_eq_singleton
    relation

/-- The trace-correspondence root exposes generated support-candidate certificate splits by ledger. -/
theorem TraceCorQ.relationGenerator_supportCandidate_certificateLedger_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.support.certificateLedger
        (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  TraceCorQRelationGenerator.supportCandidate_certificateLedger_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-candidate imported counts by ledger. -/
theorem TraceCorQ.relationGenerator_supportCandidate_importedRectangleCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangleCount =
      relation.support.importedRectangleCount +
        (TraceCorQRelationLedger.singleton relation).importedRectangleCount :=
  TraceCorQRelationGenerator.supportCandidate_importedRectangleCount_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-candidate imported rectangles by ledger. -/
theorem TraceCorQ.relationGenerator_supportCandidate_importedRectangles_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangles =
      relation.support.importedRectangles ++
        (TraceCorQRelationLedger.singleton relation).importedRectangles :=
  TraceCorQRelationGenerator.supportCandidate_importedRectangles_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-candidate bookkeeping counts by ledger. -/
theorem TraceCorQ.relationGenerator_supportCandidate_traceBookkeepingCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).traceBookkeepingCount =
      relation.support.traceBookkeepingCount +
        (TraceCorQRelationLedger.singleton relation).traceBookkeepingCount :=
  TraceCorQRelationGenerator.supportCandidate_traceBookkeepingCount_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-candidate rewrite-step counts by ledger. -/
theorem TraceCorQ.relationGenerator_supportCandidate_rewriteStepCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).rewriteStepCount =
      relation.support.rewriteStepCount +
        (TraceCorQRelationLedger.singleton relation).rewriteStepCount :=
  TraceCorQRelationGenerator.supportCandidate_rewriteStepCount_eq_support_ledger
    relation

/-- The trace-correspondence root exposes generated support-candidate count-as-length. -/
theorem TraceCorQ.relationGenerator_supportCandidate_importedRectangleCount_eq_length_importedRectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportCandidate relation).importedRectangles.length :=
  TraceCorQRelationGenerator.supportCandidate_importedRectangleCount_eq_length_importedRectangles
    relation

/-- The trace-correspondence root exposes generated support-candidate certificate splits by generator. -/
theorem TraceCorQ.relationGenerator_supportCandidate_certificateLedger_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.support.certificateLedger
        (ResidueChannelCertificateLedger.append
          relation.certificateLedger
          ResidueChannelCertificateLedger.empty) :=
  TraceCorQRelationGenerator.supportCandidate_certificateLedger_eq_support_generator
    relation

/-- The trace-correspondence root exposes generated support-candidate imported counts by generator. -/
theorem TraceCorQ.relationGenerator_supportCandidate_importedRectangleCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangleCount =
      relation.support.importedRectangleCount +
        (relation.importedRectangleCount + 0) :=
  TraceCorQRelationGenerator.supportCandidate_importedRectangleCount_eq_support_generator
    relation

/-- The trace-correspondence root exposes generated support-candidate imported rectangles by generator. -/
theorem TraceCorQ.relationGenerator_supportCandidate_importedRectangles_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangles =
      relation.support.importedRectangles ++
        (relation.importedRectangles ++ []) :=
  TraceCorQRelationGenerator.supportCandidate_importedRectangles_eq_support_generator
    relation

/-- The trace-correspondence root exposes generated support-candidate bookkeeping counts by generator. -/
theorem TraceCorQ.relationGenerator_supportCandidate_traceBookkeepingCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).traceBookkeepingCount =
      relation.support.traceBookkeepingCount +
        (relation.traceBookkeepingCount + 0) :=
  TraceCorQRelationGenerator.supportCandidate_traceBookkeepingCount_eq_support_generator
    relation

/-- The trace-correspondence root exposes generated support-candidate rewrite-step counts by generator. -/
theorem TraceCorQ.relationGenerator_supportCandidate_rewriteStepCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).rewriteStepCount =
      relation.support.rewriteStepCount +
        (relation.rewriteStepCount + 0) :=
  TraceCorQRelationGenerator.supportCandidate_rewriteStepCount_eq_support_generator
    relation

end AnalyticMotives
end LFunctions
end Boundary
