import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Endpoint.SameFormalSum.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Endpoint.PermFormalSum.Owner

/-!
# Top-root formal-sum endpoint relation-witness certificate facts
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the supplied certificate ledger for same-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_sameFormalSum_certificateLedger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).certificateLedger =
      ledger.certificateLedger :=
  TraceCorQ.relationWitness_sameFormalSum_certificateLedger
    ledger
    formalSum_eq

/-- The top root exposes the supplied imported count for same-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_sameFormalSum_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).importedRectangleCount =
      ledger.importedRectangleCount :=
  TraceCorQ.relationWitness_sameFormalSum_importedRectangleCount
    ledger
    formalSum_eq

/-- The top root exposes the supplied imported rectangles for same-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_sameFormalSum_importedRectangles
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).importedRectangles =
      ledger.importedRectangles :=
  TraceCorQ.relationWitness_sameFormalSum_importedRectangles
    ledger
    formalSum_eq

/-- The top root exposes the supplied bookkeeping count for same-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_sameFormalSum_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  TraceCorQ.relationWitness_sameFormalSum_traceBookkeepingCount
    ledger
    formalSum_eq

/-- The top root exposes the supplied rewrite-step count for same-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_sameFormalSum_rewriteStepCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).rewriteStepCount =
      ledger.rewriteStepCount :=
  TraceCorQ.relationWitness_sameFormalSum_rewriteStepCount
    ledger
    formalSum_eq

/-- The top root exposes the supplied certificate ledger for permuted-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_permFormalSum_certificateLedger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).certificateLedger =
      ledger.certificateLedger :=
  TraceCorQ.relationWitness_permFormalSum_certificateLedger
    ledger
    formalSum_perm

/-- The top root exposes the supplied imported count for permuted-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_permFormalSum_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).importedRectangleCount =
      ledger.importedRectangleCount :=
  TraceCorQ.relationWitness_permFormalSum_importedRectangleCount
    ledger
    formalSum_perm

/-- The top root exposes the supplied imported rectangles for permuted-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_permFormalSum_importedRectangles
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).importedRectangles =
      ledger.importedRectangles :=
  TraceCorQ.relationWitness_permFormalSum_importedRectangles
    ledger
    formalSum_perm

/-- The top root exposes the supplied bookkeeping count for permuted-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_permFormalSum_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  TraceCorQ.relationWitness_permFormalSum_traceBookkeepingCount
    ledger
    formalSum_perm

/-- The top root exposes the supplied rewrite-step count for permuted-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_permFormalSum_rewriteStepCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).rewriteStepCount =
      ledger.rewriteStepCount :=
  TraceCorQ.relationWitness_permFormalSum_rewriteStepCount
    ledger
    formalSum_perm

end AnalyticMotives
end LFunctions
end Boundary
