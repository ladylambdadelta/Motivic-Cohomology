import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Smul.Owner

/-!
# Public scalar relation-witness payload facts

This file exposes payload formulas for scalar compatibility witnesses between
typed trace-correspondence hom representatives.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes representative-to-candidate scalar witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulRepresentative_to_candidateSmul_certificateLedger
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).certificateLedger =
      representative.rawCandidate.ledger.certificateLedger :=
  TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_certificateLedger
    coefficient
    representative

/-- The top root exposes representative-to-candidate scalar witness imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulRepresentative_to_candidateSmul_importedRectangleCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).importedRectangleCount =
      representative.rawCandidate.ledger.importedRectangleCount :=
  TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_importedRectangleCount
    coefficient
    representative

/-- The top root exposes representative-to-candidate scalar witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulRepresentative_to_candidateSmul_importedRectangles
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).importedRectangles =
      representative.rawCandidate.ledger.importedRectangles :=
  TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_importedRectangles
    coefficient
    representative

/-- The top root exposes representative-to-candidate scalar witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulRepresentative_to_candidateSmul_traceBookkeepingCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).traceBookkeepingCount =
      representative.rawCandidate.ledger.traceBookkeepingCount :=
  TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_traceBookkeepingCount
    coefficient
    representative

/-- The top root exposes candidate-to-representative scalar witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateSmul_to_smulRepresentative_certificateLedger
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).certificateLedger =
      representative.rawCandidate.ledger.certificateLedger :=
  TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_certificateLedger
    coefficient
    representative

/-- The top root exposes candidate-to-representative scalar witness imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateSmul_to_smulRepresentative_importedRectangleCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).importedRectangleCount =
      representative.rawCandidate.ledger.importedRectangleCount :=
  TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_importedRectangleCount
    coefficient
    representative

/-- The top root exposes candidate-to-representative scalar witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateSmul_to_smulRepresentative_importedRectangles
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).importedRectangles =
      representative.rawCandidate.ledger.importedRectangles :=
  TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_importedRectangles
    coefficient
    representative

/-- The top root exposes candidate-to-representative scalar witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateSmul_to_smulRepresentative_traceBookkeepingCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).traceBookkeepingCount =
      representative.rawCandidate.ledger.traceBookkeepingCount :=
  TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_traceBookkeepingCount
    coefficient
    representative

/-- The top root exposes scalar congruence witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulCongr_certificateLedger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.rawCandidate.ledger.certificateLedger
        (ResidueChannelCertificateLedger.append
          witness.certificateLedger
          right.rawCandidate.ledger.certificateLedger) :=
  TraceCorQHomRelationWitness.smulCongr_certificateLedger
    coefficient
    witness

/-- The top root exposes scalar congruence witness imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulCongr_importedRectangleCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).importedRectangleCount =
      left.rawCandidate.ledger.importedRectangleCount +
        (witness.importedRectangleCount +
          right.rawCandidate.ledger.importedRectangleCount) :=
  TraceCorQHomRelationWitness.smulCongr_importedRectangleCount
    coefficient
    witness

/-- The top root exposes scalar congruence witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulCongr_importedRectangles
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).importedRectangles =
      left.rawCandidate.ledger.importedRectangles ++
        (witness.importedRectangles ++
          right.rawCandidate.ledger.importedRectangles) :=
  TraceCorQHomRelationWitness.smulCongr_importedRectangles
    coefficient
    witness

/-- The top root exposes scalar congruence witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulCongr_traceBookkeepingCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).traceBookkeepingCount =
      left.rawCandidate.ledger.traceBookkeepingCount +
        (witness.traceBookkeepingCount +
          right.rawCandidate.ledger.traceBookkeepingCount) :=
  TraceCorQHomRelationWitness.smulCongr_traceBookkeepingCount
    coefficient
    witness

/-- The top root exposes scalar congruence witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulCongr_rewriteStepCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).rewriteStepCount =
      left.rawCandidate.ledger.rewriteStepCount +
        (witness.rewriteStepCount +
          right.rawCandidate.ledger.rewriteStepCount) :=
  TraceCorQHomRelationWitness.smulCongr_rewriteStepCount
    coefficient
    witness

end AnalyticMotives
end LFunctions
end Boundary
