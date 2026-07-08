import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Payload.OperationLengths.Owner

/-!
# Public payload facts for typed hom relation witnesses

This file exposes certificate-ledger projections and imported-rectangle length
facts for typed trace-correspondence hom relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes relation-witness imported counts from certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_importedRectangleCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangleCount =
      witness.certificateLedger.importedRectangleCount :=
  TraceCorQHomRelationWitness.importedRectangleCount_eq_certificateLedger_count
    witness

/-- The top root exposes relation-witness imported rectangles from certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_importedRectangles_eq_certificateLedger_rectangles
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangles =
      witness.certificateLedger.importedRectangles :=
  TraceCorQHomRelationWitness.importedRectangles_eq_certificateLedger_rectangles
    witness

/-- The top root exposes relation-witness bookkeeping counts from certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_traceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.certificateLedger.traceBookkeepingCount :=
  TraceCorQHomRelationWitness.traceBookkeepingCount_eq_certificateLedger_count
    witness

/-- The top root exposes relation-witness rewrite-step counts from certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_rewriteStepCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.rewriteStepCount =
      witness.certificateLedger.rewriteStepCount :=
  TraceCorQHomRelationWitness.rewriteStepCount_eq_certificateLedger_count
    witness

/-- The top root exposes reflexive witness imported count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_refl_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).importedRectangleCount =
      (TraceCorQHomRelationWitness.refl representative).importedRectangles.length :=
  TraceCorQHomRelationWitness.refl_importedRectangleCount_eq_length
    representative

/-- The top root exposes symmetric witness imported count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_symm_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).importedRectangleCount =
      (TraceCorQHomRelationWitness.symm witness).importedRectangles.length :=
  TraceCorQHomRelationWitness.symm_importedRectangleCount_eq_length
    witness

/-- The top root exposes transitive witness imported count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_trans_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).importedRectangleCount =
      (TraceCorQHomRelationWitness.trans first second).importedRectangles.length :=
  TraceCorQHomRelationWitness.trans_importedRectangleCount_eq_length
    first
    second

/-- The top root exposes representative-to-candidate add witness count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addRepresentative_to_candidateAdd_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).importedRectangleCount =
      (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
        left
        right).importedRectangles.length :=
  TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_importedRectangleCount_eq_length
    left
    right

/-- The top root exposes candidate-to-representative add witness count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateAdd_to_addRepresentative_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).importedRectangleCount =
      (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
        left
        right).importedRectangles.length :=
  TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_importedRectangleCount_eq_length
    left
    right

/-- The top root exposes additive congruence witness count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addCongr_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left₁ left₂ right₁ right₂ : TraceCorQHomRepresentative source target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.addCongr
      leftWitness
      rightWitness).importedRectangleCount =
      (TraceCorQHomRelationWitness.addCongr
        leftWitness
        rightWitness).importedRectangles.length :=
  TraceCorQHomRelationWitness.addCongr_importedRectangleCount_eq_length
    leftWitness
    rightWitness

/-- The top root exposes representative-to-candidate scalar witness count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulRepresentative_to_candidateSmul_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).importedRectangleCount =
      (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
        coefficient
        representative).importedRectangles.length :=
  TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_importedRectangleCount_eq_length
    coefficient
    representative

/-- The top root exposes candidate-to-representative scalar witness count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateSmul_to_smulRepresentative_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).importedRectangleCount =
      (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
        coefficient
        representative).importedRectangles.length :=
  TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_importedRectangleCount_eq_length
    coefficient
    representative

/-- The top root exposes scalar congruence witness count as list length. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_smulCongr_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness).importedRectangleCount =
      (TraceCorQHomRelationWitness.smulCongr
        coefficient
        witness).importedRectangles.length :=
  TraceCorQHomRelationWitness.smulCongr_importedRectangleCount_eq_length
    coefficient
    witness

end AnalyticMotives
end LFunctions
end Boundary
