import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Owner

/-!
# Public scalar and composition relation-witness certificate facts

This file exposes certificate payload laws for scalar and composition
compatibility of relation witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes preservation of certificate ledgers under scalar compatibility. -/
theorem TraceCorQ.relationWitness_smulCongr_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).certificateLedger =
      witness.certificateLedger :=
  TraceCorQRelationWitness.smulCongr_certificateLedger
    coefficient
    witness

/-- The trace-correspondence root exposes preservation of imported counts under scalar compatibility. -/
theorem TraceCorQ.relationWitness_smulCongr_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).importedRectangleCount =
      witness.importedRectangleCount :=
  TraceCorQRelationWitness.smulCongr_importedRectangleCount
    coefficient
    witness

/-- The trace-correspondence root exposes preservation of imported rectangles under scalar compatibility. -/
theorem TraceCorQ.relationWitness_smulCongr_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).importedRectangles =
      witness.importedRectangles :=
  TraceCorQRelationWitness.smulCongr_importedRectangles
    coefficient
    witness

/-- The trace-correspondence root exposes preservation of bookkeeping counts under scalar compatibility. -/
theorem TraceCorQ.relationWitness_smulCongr_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  TraceCorQRelationWitness.smulCongr_traceBookkeepingCount
    coefficient
    witness

/-- The trace-correspondence root exposes preservation of rewrite-step counts under scalar compatibility. -/
theorem TraceCorQ.relationWitness_smulCongr_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).rewriteStepCount =
      witness.rewriteStepCount :=
  TraceCorQRelationWitness.smulCongr_rewriteStepCount
    coefficient
    witness

/-- The trace-correspondence root exposes append of certificate ledgers under composition compatibility. -/
theorem TraceCorQ.relationWitness_compCongr_certificateLedger
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).certificateLedger =
      ResidueChannelCertificateLedger.append
        leftWitness.certificateLedger
        rightWitness.certificateLedger :=
  TraceCorQRelationWitness.compCongr_certificateLedger
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes addition of imported counts under composition compatibility. -/
theorem TraceCorQ.relationWitness_compCongr_importedRectangleCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).importedRectangleCount =
      leftWitness.importedRectangleCount +
        rightWitness.importedRectangleCount :=
  TraceCorQRelationWitness.compCongr_importedRectangleCount
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes concatenation of imported rectangles under composition compatibility. -/
theorem TraceCorQ.relationWitness_compCongr_importedRectangles
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).importedRectangles =
      leftWitness.importedRectangles ++
        rightWitness.importedRectangles :=
  TraceCorQRelationWitness.compCongr_importedRectangles
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes addition of bookkeeping counts under composition compatibility. -/
theorem TraceCorQ.relationWitness_compCongr_traceBookkeepingCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).traceBookkeepingCount =
      leftWitness.traceBookkeepingCount +
        rightWitness.traceBookkeepingCount :=
  TraceCorQRelationWitness.compCongr_traceBookkeepingCount
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes addition of rewrite-step counts under composition compatibility. -/
theorem TraceCorQ.relationWitness_compCongr_rewriteStepCount
    {leftA leftB rightA rightB : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftA leftB)
    (rightWitness : TraceCorQRelationWitness rightA rightB) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).rewriteStepCount =
      leftWitness.rewriteStepCount +
        rightWitness.rewriteStepCount :=
  TraceCorQRelationWitness.compCongr_rewriteStepCount
    leftWitness
    rightWitness

end AnalyticMotives
end LFunctions
end Boundary
