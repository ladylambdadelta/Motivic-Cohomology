import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Endpoint.Owner

/-!
# Public endpoint-transport certificate facts

This file exposes certificate payload preservation laws for endpoint-transported
relation witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes preservation of certificate ledgers under endpoint transport. -/
theorem TraceCorQ.relationWitness_transportEndpoints_certificateLedger
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
  TraceCorQRelationWitness.transportEndpoints_certificateLedger
    left_eq
    right_eq
    witness

/-- The trace-correspondence root exposes preservation of imported counts under endpoint transport. -/
theorem TraceCorQ.relationWitness_transportEndpoints_importedRectangleCount
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
  TraceCorQRelationWitness.transportEndpoints_importedRectangleCount
    left_eq
    right_eq
    witness

/-- The trace-correspondence root exposes preservation of imported rectangles under endpoint transport. -/
theorem TraceCorQ.relationWitness_transportEndpoints_importedRectangles
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
  TraceCorQRelationWitness.transportEndpoints_importedRectangles
    left_eq
    right_eq
    witness

/-- The trace-correspondence root exposes preservation of bookkeeping counts under endpoint transport. -/
theorem TraceCorQ.relationWitness_transportEndpoints_traceBookkeepingCount
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
  TraceCorQRelationWitness.transportEndpoints_traceBookkeepingCount
    left_eq
    right_eq
    witness

/-- The trace-correspondence root exposes preservation of rewrite-step counts under endpoint transport. -/
theorem TraceCorQ.relationWitness_transportEndpoints_rewriteStepCount
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
  TraceCorQRelationWitness.transportEndpoints_rewriteStepCount
    left_eq
    right_eq
    witness

end AnalyticMotives
end LFunctions
end Boundary
