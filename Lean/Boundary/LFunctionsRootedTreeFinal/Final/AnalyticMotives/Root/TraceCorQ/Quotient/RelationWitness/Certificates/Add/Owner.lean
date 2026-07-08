import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Add.Owner

/-!
# Top-root additive relation-witness certificate facts

This file exposes the concrete certificate payload laws for additive
compatibility of relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes append of certificate ledgers under additive compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_addCongr_certificateLedger
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).certificateLedger =
      ResidueChannelCertificateLedger.append
        leftWitness.certificateLedger
        rightWitness.certificateLedger :=
  TraceCorQ.relationWitness_addCongr_certificateLedger
    leftWitness
    rightWitness

/-- The top root exposes addition of imported counts under additive compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_addCongr_importedRectangleCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).importedRectangleCount =
      leftWitness.importedRectangleCount +
        rightWitness.importedRectangleCount :=
  TraceCorQ.relationWitness_addCongr_importedRectangleCount
    leftWitness
    rightWitness

/-- The top root exposes concatenation of imported rectangles under additive compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_addCongr_importedRectangles
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).importedRectangles =
      leftWitness.importedRectangles ++
        rightWitness.importedRectangles :=
  TraceCorQ.relationWitness_addCongr_importedRectangles
    leftWitness
    rightWitness

/-- The top root exposes addition of bookkeeping counts under additive compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_addCongr_traceBookkeepingCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).traceBookkeepingCount =
      leftWitness.traceBookkeepingCount +
        rightWitness.traceBookkeepingCount :=
  TraceCorQ.relationWitness_addCongr_traceBookkeepingCount
    leftWitness
    rightWitness

/-- The top root exposes addition of rewrite-step counts under additive compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_addCongr_rewriteStepCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).rewriteStepCount =
      leftWitness.rewriteStepCount +
        rightWitness.rewriteStepCount :=
  TraceCorQ.relationWitness_addCongr_rewriteStepCount
    leftWitness
    rightWitness

end AnalyticMotives
end LFunctions
end Boundary
