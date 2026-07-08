import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Certificates.Endpoint.FormalSum.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Endpoint.CancelAdjacentOpposite.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Endpoint.CombineAdjacentSame.Owner

/-!
# Top-root adjacent endpoint relation-witness certificate facts
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the supplied certificate ledger for adjacent cancellation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_cancelAdjacentOpposite_certificateLedger
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
  TraceCorQ.relationWitness_cancelAdjacentOpposite_certificateLedger
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The top root exposes the supplied imported count for adjacent cancellation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_cancelAdjacentOpposite_importedRectangleCount
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
  TraceCorQ.relationWitness_cancelAdjacentOpposite_importedRectangleCount
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The top root exposes the supplied imported rectangles for adjacent cancellation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_cancelAdjacentOpposite_importedRectangles
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
  TraceCorQ.relationWitness_cancelAdjacentOpposite_importedRectangles
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The top root exposes the supplied bookkeeping count for adjacent cancellation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_cancelAdjacentOpposite_traceBookkeepingCount
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
  TraceCorQ.relationWitness_cancelAdjacentOpposite_traceBookkeepingCount
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The top root exposes the supplied rewrite-step count for adjacent cancellation. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_cancelAdjacentOpposite_rewriteStepCount
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
  TraceCorQ.relationWitness_cancelAdjacentOpposite_rewriteStepCount
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The top root exposes the supplied certificate ledger for adjacent combination. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_combineAdjacentSame_certificateLedger
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
  TraceCorQ.relationWitness_combineAdjacentSame_certificateLedger
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The top root exposes the supplied imported count for adjacent combination. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_combineAdjacentSame_importedRectangleCount
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
  TraceCorQ.relationWitness_combineAdjacentSame_importedRectangleCount
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The top root exposes the supplied imported rectangles for adjacent combination. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_combineAdjacentSame_importedRectangles
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
  TraceCorQ.relationWitness_combineAdjacentSame_importedRectangles
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The top root exposes the supplied bookkeeping count for adjacent combination. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_combineAdjacentSame_traceBookkeepingCount
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
  TraceCorQ.relationWitness_combineAdjacentSame_traceBookkeepingCount
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The top root exposes the supplied rewrite-step count for adjacent combination. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_combineAdjacentSame_rewriteStepCount
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
  TraceCorQ.relationWitness_combineAdjacentSame_rewriteStepCount
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

end AnalyticMotives
end LFunctions
end Boundary
