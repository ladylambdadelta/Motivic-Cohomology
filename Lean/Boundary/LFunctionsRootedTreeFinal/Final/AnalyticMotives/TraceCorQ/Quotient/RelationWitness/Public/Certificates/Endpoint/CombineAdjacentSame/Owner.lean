import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Endpoint.Owner

/-!
# Public adjacent-combination endpoint certificate facts

This file exposes certificate payload laws for adjacent same-generator
coefficient-combination relation witnesses under the `TraceCorQ` aggregate
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the supplied certificate ledger for adjacent combination. -/
theorem TraceCorQ.relationWitness_combineAdjacentSame_certificateLedger
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.combineAdjacentSame
      ledger
      leftContext
      suffix
      leftCoefficient
      rightCoefficient
      generator).certificateLedger =
      ledger.certificateLedger :=
  TraceCorQRelationWitness.combineAdjacentSame_certificateLedger
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The trace-correspondence root exposes the supplied imported count for adjacent combination. -/
theorem TraceCorQ.relationWitness_combineAdjacentSame_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.combineAdjacentSame
      ledger
      leftContext
      suffix
      leftCoefficient
      rightCoefficient
      generator).importedRectangleCount =
      ledger.importedRectangleCount :=
  TraceCorQRelationWitness.combineAdjacentSame_importedRectangleCount
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The trace-correspondence root exposes the supplied imported rectangles for adjacent combination. -/
theorem TraceCorQ.relationWitness_combineAdjacentSame_importedRectangles
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.combineAdjacentSame
      ledger
      leftContext
      suffix
      leftCoefficient
      rightCoefficient
      generator).importedRectangles =
      ledger.importedRectangles :=
  TraceCorQRelationWitness.combineAdjacentSame_importedRectangles
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The trace-correspondence root exposes the supplied bookkeeping count for adjacent combination. -/
theorem TraceCorQ.relationWitness_combineAdjacentSame_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.combineAdjacentSame
      ledger
      leftContext
      suffix
      leftCoefficient
      rightCoefficient
      generator).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.combineAdjacentSame_traceBookkeepingCount
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The trace-correspondence root exposes the supplied rewrite-step count for adjacent combination. -/
theorem TraceCorQ.relationWitness_combineAdjacentSame_rewriteStepCount
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.combineAdjacentSame
      ledger
      leftContext
      suffix
      leftCoefficient
      rightCoefficient
      generator).rewriteStepCount =
      ledger.rewriteStepCount :=
  TraceCorQRelationWitness.combineAdjacentSame_rewriteStepCount
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

end AnalyticMotives
end LFunctions
end Boundary
