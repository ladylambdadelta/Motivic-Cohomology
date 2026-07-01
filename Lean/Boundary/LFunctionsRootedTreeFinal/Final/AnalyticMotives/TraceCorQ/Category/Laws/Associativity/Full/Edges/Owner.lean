import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Typed.Owner

/-!
# Fourfold associativity edges for typed trace-correspondence composition

This file owns the elementary reassociation edges between the five
parenthesizations of a fourfold typed composite.  The full normalization file
composes these edges into right-associated normal forms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Move the outer three factors of a fully left-associated typed composite. -/
theorem TraceCorQHom.comp_assoc_four_left_outer_edge
    {first second third fourth fifth : TraceCorQObject}
    (firstMap : TraceCorQHom first second)
    (secondMap : TraceCorQHom second third)
    (thirdMap : TraceCorQHom third fourth)
    (fourthMap : TraceCorQHom fourth fifth) :
    TraceCorQHom.comp
      (TraceCorQHom.comp
        (TraceCorQHom.comp firstMap secondMap)
        thirdMap)
      fourthMap =
      TraceCorQHom.comp
        (TraceCorQHom.comp firstMap secondMap)
        (TraceCorQHom.comp thirdMap fourthMap) :=
  TraceCorQHom.comp_assoc
    (TraceCorQHom.comp firstMap secondMap)
    thirdMap
    fourthMap

/-- Move the final three factors inside a typed left head. -/
theorem TraceCorQHom.comp_assoc_four_left_inner_edge
    {first second third fourth fifth : TraceCorQObject}
    (firstMap : TraceCorQHom first second)
    (secondMap : TraceCorQHom second third)
    (thirdMap : TraceCorQHom third fourth)
    (fourthMap : TraceCorQHom fourth fifth) :
    TraceCorQHom.comp
      (TraceCorQHom.comp firstMap secondMap)
      (TraceCorQHom.comp thirdMap fourthMap) =
      TraceCorQHom.comp
        firstMap
        (TraceCorQHom.comp
          secondMap
          (TraceCorQHom.comp thirdMap fourthMap)) :=
  TraceCorQHom.comp_assoc
    firstMap
    secondMap
    (TraceCorQHom.comp thirdMap fourthMap)

/-- Move the outer factors of a typed composite whose middle pair was first. -/
theorem TraceCorQHom.comp_assoc_four_middle_left_outer_edge
    {first second third fourth fifth : TraceCorQObject}
    (firstMap : TraceCorQHom first second)
    (secondMap : TraceCorQHom second third)
    (thirdMap : TraceCorQHom third fourth)
    (fourthMap : TraceCorQHom fourth fifth) :
    TraceCorQHom.comp
      (TraceCorQHom.comp
        firstMap
        (TraceCorQHom.comp secondMap thirdMap))
      fourthMap =
      TraceCorQHom.comp
        firstMap
        (TraceCorQHom.comp
          (TraceCorQHom.comp secondMap thirdMap)
          fourthMap) :=
  TraceCorQHom.comp_assoc
    firstMap
    (TraceCorQHom.comp secondMap thirdMap)
    fourthMap

/-- Reassociate the right tail of a fourfold typed composite. -/
theorem TraceCorQHom.comp_assoc_four_tail_edge
    {first second third fourth fifth : TraceCorQObject}
    (firstMap : TraceCorQHom first second)
    (secondMap : TraceCorQHom second third)
    (thirdMap : TraceCorQHom third fourth)
    (fourthMap : TraceCorQHom fourth fifth) :
    TraceCorQHom.comp
      firstMap
      (TraceCorQHom.comp
        (TraceCorQHom.comp secondMap thirdMap)
        fourthMap) =
      TraceCorQHom.comp
        firstMap
        (TraceCorQHom.comp
          secondMap
          (TraceCorQHom.comp thirdMap fourthMap)) :=
  congrArg
    (fun tail =>
      TraceCorQHom.comp firstMap tail)
    (TraceCorQHom.comp_assoc
      secondMap
      thirdMap
      fourthMap)

end AnalyticMotives
end LFunctions
end Boundary
