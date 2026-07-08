import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Payload.Lengths.Owner

/-!
# Operation relation-witness payload length facts

This file owns imported-rectangle length invariants for typed hom
relation-witness constructors induced by addition and scalar multiplication.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Representative-to-candidate addition has count equal to rectangle-list length. -/
theorem TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).importedRectangleCount =
      (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
        left
        right).importedRectangles.length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right)

/-- Candidate-to-representative addition has count equal to rectangle-list length. -/
theorem TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).importedRectangleCount =
      (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
        left
        right).importedRectangles.length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right)

/-- Additive congruence has count equal to rectangle-list length. -/
theorem TraceCorQHomRelationWitness.addCongr_importedRectangleCount_eq_length
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
  TraceCorQHomRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRelationWitness.addCongr
      leftWitness
      rightWitness)

/-- Representative-to-candidate scalar multiplication has count equal to rectangle-list length. -/
theorem TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative).importedRectangleCount =
      (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
        coefficient
        representative).importedRectangles.length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRelationWitness.smulRepresentative_to_candidateSmul
      coefficient
      representative)

/-- Candidate-to-representative scalar multiplication has count equal to rectangle-list length. -/
theorem TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative).importedRectangleCount =
      (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
        coefficient
        representative).importedRectangles.length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRelationWitness.candidateSmul_to_smulRepresentative
      coefficient
      representative)

/-- Scalar congruence has count equal to rectangle-list length. -/
theorem TraceCorQHomRelationWitness.smulCongr_importedRectangleCount_eq_length
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
  TraceCorQHomRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRelationWitness.smulCongr
      coefficient
      witness)

end AnalyticMotives
end LFunctions
end Boundary
