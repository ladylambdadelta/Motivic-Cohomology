import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Owner

/-!
# Endpoint relation-witness certificate payloads

This file owns certificate-payload facts for relation witnesses whose
certificate ledger is supplied externally or preserved by endpoint transport:
same formal sums, formal-sum permutations, adjacent cancellations, adjacent
combinations, and endpoint transports.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Same-formal-sum witnesses carry the supplied ledger's certificates. -/
theorem TraceCorQRelationWitness.sameFormalSum_certificateLedger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).certificateLedger =
      ledger.certificateLedger :=
  rfl

/-- Same-formal-sum witnesses carry the supplied ledger's imported payload. -/
theorem TraceCorQRelationWitness.sameFormalSum_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).importedRectangleCount =
      ledger.importedRectangleCount :=
  rfl

/-- Same-formal-sum witnesses expose the supplied ledger's imported rectangles. -/
theorem TraceCorQRelationWitness.sameFormalSum_importedRectangles
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).importedRectangles =
      ledger.importedRectangles :=
  rfl

/-- Same-formal-sum witnesses carry the supplied ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.sameFormalSum_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  rfl

/-- Same-formal-sum witnesses carry the supplied ledger's rewrite-step payload. -/
theorem TraceCorQRelationWitness.sameFormalSum_rewriteStepCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).rewriteStepCount =
      ledger.rewriteStepCount :=
  rfl

/-- Permuted-formal-sum witnesses carry the supplied ledger's certificates. -/
theorem TraceCorQRelationWitness.permFormalSum_certificateLedger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).certificateLedger =
      ledger.certificateLedger :=
  rfl

/-- Permuted-formal-sum witnesses carry the supplied ledger's imported payload. -/
theorem TraceCorQRelationWitness.permFormalSum_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).importedRectangleCount =
      ledger.importedRectangleCount :=
  rfl

/-- Permuted-formal-sum witnesses expose the supplied ledger's imported rectangles. -/
theorem TraceCorQRelationWitness.permFormalSum_importedRectangles
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).importedRectangles =
      ledger.importedRectangles :=
  rfl

/-- Permuted-formal-sum witnesses carry the supplied ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.permFormalSum_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  rfl

/-- Permuted-formal-sum witnesses carry the supplied ledger's rewrite-step payload. -/
theorem TraceCorQRelationWitness.permFormalSum_rewriteStepCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).rewriteStepCount =
      ledger.rewriteStepCount :=
  rfl

/-- Adjacent opposite coefficient cancellation carries the supplied ledger's certificates. -/
theorem TraceCorQRelationWitness.cancelAdjacentOpposite_certificateLedger
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
  rfl

/-- Adjacent opposite coefficient cancellation carries the supplied ledger's imported payload. -/
theorem TraceCorQRelationWitness.cancelAdjacentOpposite_importedRectangleCount
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
  rfl

/-- Adjacent opposite coefficient cancellation exposes the supplied ledger's rectangles. -/
theorem TraceCorQRelationWitness.cancelAdjacentOpposite_importedRectangles
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
  rfl

/-- Adjacent opposite coefficient cancellation carries the supplied ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.cancelAdjacentOpposite_traceBookkeepingCount
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
  rfl

/-- Adjacent opposite coefficient cancellation carries the supplied ledger's rewrite-step payload. -/
theorem TraceCorQRelationWitness.cancelAdjacentOpposite_rewriteStepCount
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
  rfl

/-- Adjacent same-generator combination carries the supplied ledger's certificates. -/
theorem TraceCorQRelationWitness.combineAdjacentSame_certificateLedger
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
  rfl

/-- Adjacent same-generator combination carries the supplied ledger's imported payload. -/
theorem TraceCorQRelationWitness.combineAdjacentSame_importedRectangleCount
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
  rfl

/-- Adjacent same-generator combination exposes the supplied ledger's imported rectangles. -/
theorem TraceCorQRelationWitness.combineAdjacentSame_importedRectangles
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
  rfl

/-- Adjacent same-generator combination carries the supplied ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.combineAdjacentSame_traceBookkeepingCount
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
  rfl

/-- Adjacent same-generator combination carries the supplied ledger's rewrite-step payload. -/
theorem TraceCorQRelationWitness.combineAdjacentSame_rewriteStepCount
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
  rfl

/-- Endpoint transport preserves witness certificate ledgers. -/
theorem TraceCorQRelationWitness.transportEndpoints_certificateLedger
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    (TraceCorQRelationWitness.transportEndpoints
      left_eq
      right_eq
      witness).certificateLedger =
      witness.certificateLedger :=
  rfl

/-- Endpoint transport preserves witness imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.transportEndpoints_importedRectangleCount
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    (TraceCorQRelationWitness.transportEndpoints
      left_eq
      right_eq
      witness).importedRectangleCount =
      witness.importedRectangleCount :=
  rfl

/-- Endpoint transport preserves witness imported finite explicit-formula rectangles. -/
theorem TraceCorQRelationWitness.transportEndpoints_importedRectangles
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    (TraceCorQRelationWitness.transportEndpoints
      left_eq
      right_eq
      witness).importedRectangles =
      witness.importedRectangles :=
  rfl

/-- Endpoint transport preserves witness internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.transportEndpoints_traceBookkeepingCount
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    (TraceCorQRelationWitness.transportEndpoints
      left_eq
      right_eq
      witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  rfl

/-- Endpoint transport preserves witness explicit rewrite-step payload. -/
theorem TraceCorQRelationWitness.transportEndpoints_rewriteStepCount
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    (TraceCorQRelationWitness.transportEndpoints
      left_eq
      right_eq
      witness).rewriteStepCount =
      witness.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
