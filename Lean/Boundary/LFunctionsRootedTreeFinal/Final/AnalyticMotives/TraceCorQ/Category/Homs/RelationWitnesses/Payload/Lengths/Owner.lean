import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Payload.Owner

/-!
# Typed hom relation-witness payload length facts

This file owns imported-rectangle length invariants for the constructors of
typed hom relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A reflexive typed hom relation witness has count equal to rectangle-list length. -/
theorem TraceCorQHomRelationWitness.refl_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).importedRectangleCount =
      (TraceCorQHomRelationWitness.refl representative).importedRectangles.length :=
  TraceCorQHomRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRelationWitness.refl representative)

/-- A symmetric typed hom relation witness has count equal to rectangle-list length. -/
theorem TraceCorQHomRelationWitness.symm_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).importedRectangleCount =
      (TraceCorQHomRelationWitness.symm witness).importedRectangles.length :=
  TraceCorQHomRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRelationWitness.symm witness)

/-- A transitive typed hom relation witness has count equal to rectangle-list length. -/
theorem TraceCorQHomRelationWitness.trans_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).importedRectangleCount =
      (TraceCorQHomRelationWitness.trans first second).importedRectangles.length :=
  TraceCorQHomRelationWitness.importedRectangleCount_eq_length_importedRectangles
    (TraceCorQHomRelationWitness.trans first second)

end AnalyticMotives
end LFunctions
end Boundary
