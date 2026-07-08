import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Endpoint.Owner

/-!
# Public adjacent-cancellation endpoint certificate facts

This file exposes certificate payload laws for adjacent opposite-coefficient
cancellation relation witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the supplied certificate ledger for adjacent cancellation. -/
theorem TraceCorQ.relationWitness_cancelAdjacentOpposite_certificateLedger
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.cancelAdjacentOpposite
      ledger
      leftContext
      suffix
      coefficient
      generator).certificateLedger =
      ledger.certificateLedger :=
  TraceCorQRelationWitness.cancelAdjacentOpposite_certificateLedger
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The trace-correspondence root exposes the supplied imported count for adjacent cancellation. -/
theorem TraceCorQ.relationWitness_cancelAdjacentOpposite_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.cancelAdjacentOpposite
      ledger
      leftContext
      suffix
      coefficient
      generator).importedRectangleCount =
      ledger.importedRectangleCount :=
  TraceCorQRelationWitness.cancelAdjacentOpposite_importedRectangleCount
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The trace-correspondence root exposes the supplied imported rectangles for adjacent cancellation. -/
theorem TraceCorQ.relationWitness_cancelAdjacentOpposite_importedRectangles
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.cancelAdjacentOpposite
      ledger
      leftContext
      suffix
      coefficient
      generator).importedRectangles =
      ledger.importedRectangles :=
  TraceCorQRelationWitness.cancelAdjacentOpposite_importedRectangles
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The trace-correspondence root exposes the supplied bookkeeping count for adjacent cancellation. -/
theorem TraceCorQ.relationWitness_cancelAdjacentOpposite_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.cancelAdjacentOpposite
      ledger
      leftContext
      suffix
      coefficient
      generator).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.cancelAdjacentOpposite_traceBookkeepingCount
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The trace-correspondence root exposes the supplied rewrite-step count for adjacent cancellation. -/
theorem TraceCorQ.relationWitness_cancelAdjacentOpposite_rewriteStepCount
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.cancelAdjacentOpposite
      ledger
      leftContext
      suffix
      coefficient
      generator).rewriteStepCount =
      ledger.rewriteStepCount :=
  TraceCorQRelationWitness.cancelAdjacentOpposite_rewriteStepCount
    ledger
    leftContext
    suffix
    coefficient
    generator

end AnalyticMotives
end LFunctions
end Boundary
