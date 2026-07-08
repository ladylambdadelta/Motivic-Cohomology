import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Add.Owner

/-!
# Public additive relation-witness certificate facts

This file exposes certificate payload laws for additive compatibility of
relation witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes append of certificate ledgers under additive compatibility. -/
theorem TraceCorQ.relationWitness_addCongr_certificateLedger
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).certificateLedger =
      ResidueChannelCertificateLedger.append
        leftWitness.certificateLedger
        rightWitness.certificateLedger :=
  TraceCorQRelationWitness.addCongr_certificateLedger
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes addition of imported counts under additive compatibility. -/
theorem TraceCorQ.relationWitness_addCongr_importedRectangleCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).importedRectangleCount =
      leftWitness.importedRectangleCount +
        rightWitness.importedRectangleCount :=
  TraceCorQRelationWitness.addCongr_importedRectangleCount
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes concatenation of imported rectangles under additive compatibility. -/
theorem TraceCorQ.relationWitness_addCongr_importedRectangles
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).importedRectangles =
      leftWitness.importedRectangles ++
        rightWitness.importedRectangles :=
  TraceCorQRelationWitness.addCongr_importedRectangles
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes addition of bookkeeping counts under additive compatibility. -/
theorem TraceCorQ.relationWitness_addCongr_traceBookkeepingCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).traceBookkeepingCount =
      leftWitness.traceBookkeepingCount +
        rightWitness.traceBookkeepingCount :=
  TraceCorQRelationWitness.addCongr_traceBookkeepingCount
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes addition of rewrite-step counts under additive compatibility. -/
theorem TraceCorQ.relationWitness_addCongr_rewriteStepCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).rewriteStepCount =
      leftWitness.rewriteStepCount +
        rightWitness.rewriteStepCount :=
  TraceCorQRelationWitness.addCongr_rewriteStepCount
    leftWitness
    rightWitness

end AnalyticMotives
end LFunctions
end Boundary
