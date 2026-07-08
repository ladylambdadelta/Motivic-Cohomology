import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Owner

/-!
# Payload projections for generated support inputs

This file records the analytic payload carried by the pre-quotient input
attached to a single relation generator.  That input is the generator's formal
support equipped with the singleton relation ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A generated support input has formal support from its relation generator. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_formalSum_eq_support
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).formalSum =
      relation.support :=
  TraceCorQRelationGenerator.supportQuotientInput_formalSum relation

/-- A generated support input has the singleton relation ledger. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_ledger_eq_singleton
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).ledger =
      TraceCorQRelationLedger.singleton relation :=
  TraceCorQRelationGenerator.supportQuotientInput_ledger relation

/-- A generated support input's certificate ledger splits into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_certificateLedger_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.support.certificateLedger
        (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  TraceCorQQuotientInput.ofFormalSumLedger_certificateLedger
    relation.support
    (TraceCorQRelationLedger.singleton relation)

/-- A generated support input's imported count splits into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_importedRectangleCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangleCount =
      relation.support.importedRectangleCount +
        (TraceCorQRelationLedger.singleton relation).importedRectangleCount :=
  TraceCorQQuotientInput.ofFormalSumLedger_importedRectangleCount
    relation.support
    (TraceCorQRelationLedger.singleton relation)

/-- A generated support input's imported rectangles split into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_importedRectangles_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangles =
      relation.support.importedRectangles ++
        (TraceCorQRelationLedger.singleton relation).importedRectangles :=
  TraceCorQQuotientInput.ofFormalSumLedger_importedRectangles
    relation.support
    (TraceCorQRelationLedger.singleton relation)

/-- A generated support input's bookkeeping count splits into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_traceBookkeepingCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).traceBookkeepingCount =
      relation.support.traceBookkeepingCount +
        (TraceCorQRelationLedger.singleton relation).traceBookkeepingCount :=
  TraceCorQQuotientInput.ofFormalSumLedger_traceBookkeepingCount
    relation.support
    (TraceCorQRelationLedger.singleton relation)

/-- A generated support input's rewrite-step count splits into support and singleton ledger. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_rewriteStepCount_eq_support_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).rewriteStepCount =
      relation.support.rewriteStepCount +
        (TraceCorQRelationLedger.singleton relation).rewriteStepCount :=
  TraceCorQQuotientInput.ofFormalSumLedger_rewriteStepCount
    relation.support
    (TraceCorQRelationLedger.singleton relation)

/-- A generated support input's imported count is the length of its rectangle list. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_importedRectangleCount_eq_length_importedRectangles
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangles.length :=
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQRelationGenerator.supportQuotientInput relation)

/-- A generated support input's certificate ledger exposes support certificates and generator certificates. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_certificateLedger_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.support.certificateLedger
        (ResidueChannelCertificateLedger.append
          relation.certificateLedger
          ResidueChannelCertificateLedger.empty) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportQuotientInput_certificateLedger_eq_support_ledger
      relation)
    (congrArg
      (fun ledger =>
        ResidueChannelCertificateLedger.append
          relation.support.certificateLedger
          ledger)
      (TraceCorQRelationLedger.singleton_certificateLedger relation))

/-- A generated support input's imported count exposes support count and generator count. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_importedRectangleCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangleCount =
      relation.support.importedRectangleCount +
        (relation.importedRectangleCount + 0) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportQuotientInput_importedRectangleCount_eq_support_ledger
      relation)
    (congrArg
      (fun count => relation.support.importedRectangleCount + count)
      (TraceCorQRelationLedger.singleton_importedRectangleCount relation))

/-- A generated support input's imported rectangles expose support rectangles and generator rectangles. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_importedRectangles_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).importedRectangles =
      relation.support.importedRectangles ++
        (relation.importedRectangles ++ []) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportQuotientInput_importedRectangles_eq_support_ledger
      relation)
    (congrArg
      (fun rectangles => relation.support.importedRectangles ++ rectangles)
      (TraceCorQRelationLedger.singleton_importedRectangles relation))

/-- A generated support input's bookkeeping count exposes support count and generator count. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_traceBookkeepingCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).traceBookkeepingCount =
      relation.support.traceBookkeepingCount +
        (relation.traceBookkeepingCount + 0) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportQuotientInput_traceBookkeepingCount_eq_support_ledger
      relation)
    (congrArg
      (fun count => relation.support.traceBookkeepingCount + count)
      (TraceCorQRelationLedger.singleton_traceBookkeepingCount relation))

/-- A generated support input's rewrite-step count exposes support count and generator count. -/
theorem TraceCorQRelationGenerator.supportQuotientInput_rewriteStepCount_eq_support_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportQuotientInput relation).rewriteStepCount =
      relation.support.rewriteStepCount +
        (relation.rewriteStepCount + 0) :=
  Eq.trans
    (TraceCorQRelationGenerator.supportQuotientInput_rewriteStepCount_eq_support_ledger
      relation)
    (congrArg
      (fun count => relation.support.rewriteStepCount + count)
      (TraceCorQRelationLedger.singleton_rewriteStepCount relation))

end AnalyticMotives
end LFunctions
end Boundary
