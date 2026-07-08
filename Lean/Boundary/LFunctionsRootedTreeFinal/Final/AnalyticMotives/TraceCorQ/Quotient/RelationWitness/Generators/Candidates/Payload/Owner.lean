import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Owner

/-!
# Payload projections for generated support candidates

This file records the analytic payload carried by the support candidate of a
single relation generator.  The support candidate is the pre-quotient formal
support equipped with the singleton relation ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A generated support candidate has formal support from its relation generator. -/
theorem TraceCorQRelationGenerator.supportCandidate_formalSum_eq_support
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).formalSum =
      relation.support :=
  TraceCorQRelationGenerator.supportCandidate_formalSum relation

/-- A generated support candidate has the singleton relation ledger. -/
theorem TraceCorQRelationGenerator.supportCandidate_ledger_eq_singleton
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).ledger =
      TraceCorQRelationLedger.singleton relation :=
  TraceCorQRelationGenerator.supportCandidate_ledger relation

/-- A generated support candidate's certificate ledger splits into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportCandidate_certificateLedger_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.support.certificateLedger
        (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.supportCandidate relation)

/-- A generated support candidate's imported count splits into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportCandidate_importedRectangleCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangleCount =
      relation.support.importedRectangleCount +
        (TraceCorQRelationLedger.singleton relation).importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.supportCandidate relation)

/-- A generated support candidate's imported rectangles split into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportCandidate_importedRectangles_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangles =
      relation.support.importedRectangles ++
        (TraceCorQRelationLedger.singleton relation).importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.supportCandidate relation)

/-- A generated support candidate's bookkeeping count splits into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportCandidate_traceBookkeepingCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).traceBookkeepingCount =
      relation.support.traceBookkeepingCount +
        (TraceCorQRelationLedger.singleton relation).traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.supportCandidate relation)

/-- A generated support candidate's rewrite-step count splits into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportCandidate_rewriteStepCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).rewriteStepCount =
      relation.support.rewriteStepCount +
        (TraceCorQRelationLedger.singleton relation).rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.supportCandidate relation)

/-- A generated support candidate's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.supportCandidate_importedRectangleCount_eq_length_importedRectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportCandidate relation).importedRectangles.length :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.supportCandidate relation)

/-- A generated support candidate's certificate ledger exposes support certificates and generator certificates. -/
theorem TraceCorQRelationGenerator.supportCandidate_certificateLedger_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.support.certificateLedger
        (ResidueChannelCertificateLedger.append
          relation.certificateLedger
          ResidueChannelCertificateLedger.empty) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportCandidate_certificateLedger_eq_support_ledger
      relation)
    (congrArg
      (fun ledger =>
        ResidueChannelCertificateLedger.append
          relation.support.certificateLedger
          ledger)
      (TraceCorQRelationLedger.singleton_certificateLedger relation))

/-- A generated support candidate's imported count exposes support count and generator count. -/
theorem TraceCorQRelationGenerator.supportCandidate_importedRectangleCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangleCount =
      relation.support.importedRectangleCount +
        (relation.importedRectangleCount + 0) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportCandidate_importedRectangleCount_eq_support_ledger
      relation)
    (congrArg
      (fun count => relation.support.importedRectangleCount + count)
      (TraceCorQRelationLedger.singleton_importedRectangleCount relation))

/-- A generated support candidate's imported rectangles expose support rectangles and generator rectangles. -/
theorem TraceCorQRelationGenerator.supportCandidate_importedRectangles_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).importedRectangles =
      relation.support.importedRectangles ++
        (relation.importedRectangles ++ []) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportCandidate_importedRectangles_eq_support_ledger
      relation)
    (congrArg
      (fun rectangles => relation.support.importedRectangles ++ rectangles)
      (TraceCorQRelationLedger.singleton_importedRectangles relation))

/-- A generated support candidate's bookkeeping count exposes support count and generator count. -/
theorem TraceCorQRelationGenerator.supportCandidate_traceBookkeepingCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).traceBookkeepingCount =
      relation.support.traceBookkeepingCount +
        (relation.traceBookkeepingCount + 0) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportCandidate_traceBookkeepingCount_eq_support_ledger
      relation)
    (congrArg
      (fun count => relation.support.traceBookkeepingCount + count)
      (TraceCorQRelationLedger.singleton_traceBookkeepingCount relation))

/-- A generated support candidate's rewrite-step count exposes support count and generator count. -/
theorem TraceCorQRelationGenerator.supportCandidate_rewriteStepCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).rewriteStepCount =
      relation.support.rewriteStepCount +
        (relation.rewriteStepCount + 0) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportCandidate_rewriteStepCount_eq_support_ledger
      relation)
    (congrArg
      (fun count => relation.support.rewriteStepCount + count)
      (TraceCorQRelationLedger.singleton_rewriteStepCount relation))

end AnalyticMotives
end LFunctions
end Boundary
