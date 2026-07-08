import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Compatibility.Owner

/-!
# Top-root scalar and composition relation-witness certificate facts

This file exposes the concrete certificate payload laws for scalar and
composition compatibility of relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes preservation of certificate ledgers under scalar compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_smulCongr_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).certificateLedger =
      witness.certificateLedger :=
  TraceCorQ.relationWitness_smulCongr_certificateLedger
    coefficient
    witness

/-- The top root exposes preservation of imported counts under scalar compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_smulCongr_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).importedRectangleCount =
      witness.importedRectangleCount :=
  TraceCorQ.relationWitness_smulCongr_importedRectangleCount
    coefficient
    witness

/-- The top root exposes preservation of imported rectangles under scalar compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_smulCongr_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).importedRectangles =
      witness.importedRectangles :=
  TraceCorQ.relationWitness_smulCongr_importedRectangles
    coefficient
    witness

/-- The top root exposes preservation of bookkeeping counts under scalar compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_smulCongr_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  TraceCorQ.relationWitness_smulCongr_traceBookkeepingCount
    coefficient
    witness

/-- The top root exposes preservation of rewrite-step counts under scalar compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_smulCongr_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).rewriteStepCount =
      witness.rewriteStepCount :=
  TraceCorQ.relationWitness_smulCongr_rewriteStepCount
    coefficient
    witness

/-- The top root exposes append of certificate ledgers under composition compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_compCongr_certificateLedger
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).certificateLedger =
      ResidueChannelCertificateLedger.append
        leftWitness.certificateLedger
        rightWitness.certificateLedger :=
  TraceCorQ.relationWitness_compCongr_certificateLedger
    leftWitness
    rightWitness

/-- The top root exposes addition of imported counts under composition compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_compCongr_importedRectangleCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).importedRectangleCount =
      leftWitness.importedRectangleCount +
        rightWitness.importedRectangleCount :=
  TraceCorQ.relationWitness_compCongr_importedRectangleCount
    leftWitness
    rightWitness

/-- The top root exposes concatenation of imported rectangles under composition compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_compCongr_importedRectangles
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).importedRectangles =
      leftWitness.importedRectangles ++
        rightWitness.importedRectangles :=
  TraceCorQ.relationWitness_compCongr_importedRectangles
    leftWitness
    rightWitness

/-- The top root exposes addition of bookkeeping counts under composition compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_compCongr_traceBookkeepingCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).traceBookkeepingCount =
      leftWitness.traceBookkeepingCount +
        rightWitness.traceBookkeepingCount :=
  TraceCorQ.relationWitness_compCongr_traceBookkeepingCount
    leftWitness
    rightWitness

/-- The top root exposes addition of rewrite-step counts under composition compatibility. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_compCongr_rewriteStepCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).rewriteStepCount =
      leftWitness.rewriteStepCount +
        rightWitness.rewriteStepCount :=
  TraceCorQ.relationWitness_compCongr_rewriteStepCount
    leftWitness
    rightWitness

end AnalyticMotives
end LFunctions
end Boundary
