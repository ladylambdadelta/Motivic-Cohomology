import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Certificates.Endpoint.Adjacent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Endpoint.Transport.Owner

/-!
# Top-root endpoint-transport relation-witness certificate facts
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes preservation of certificate ledgers under endpoint transport. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_transportEndpoints_certificateLedger
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
  TraceCorQ.relationWitness_transportEndpoints_certificateLedger
    left_eq
    right_eq
    witness

/-- The top root exposes preservation of imported counts under endpoint transport. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_transportEndpoints_importedRectangleCount
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
  TraceCorQ.relationWitness_transportEndpoints_importedRectangleCount
    left_eq
    right_eq
    witness

/-- The top root exposes preservation of imported rectangles under endpoint transport. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_transportEndpoints_importedRectangles
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
  TraceCorQ.relationWitness_transportEndpoints_importedRectangles
    left_eq
    right_eq
    witness

/-- The top root exposes preservation of bookkeeping counts under endpoint transport. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_transportEndpoints_traceBookkeepingCount
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
  TraceCorQ.relationWitness_transportEndpoints_traceBookkeepingCount
    left_eq
    right_eq
    witness

/-- The top root exposes preservation of rewrite-step counts under endpoint transport. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_transportEndpoints_rewriteStepCount
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
  TraceCorQ.relationWitness_transportEndpoints_rewriteStepCount
    left_eq
    right_eq
    witness

end AnalyticMotives
end LFunctions
end Boundary
