import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Full.Edges.Owner

/-!
# Full associativity normalization for typed trace-correspondence composition

This file owns fourfold reassociation wrappers for typed trace-correspondence
composition.  The point is to make the typed category layer consume a single
right-associated normal form instead of repeatedly exposing the ambient
quotient boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Normalize the fully left-associated fourfold composite. -/
theorem TraceCorQHom.comp_assoc_four_left
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
        firstMap
        (TraceCorQHom.comp
          secondMap
          (TraceCorQHom.comp thirdMap fourthMap)) :=
  Eq.trans
    (TraceCorQHom.comp_assoc_four_left_outer_edge
      firstMap
      secondMap
      thirdMap
      fourthMap)
    (TraceCorQHom.comp_assoc_four_left_inner_edge
      firstMap
      secondMap
      thirdMap
      fourthMap)

/-- Normalize the fourfold composite with the middle pair associated first. -/
theorem TraceCorQHom.comp_assoc_four_middle_left
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
          secondMap
          (TraceCorQHom.comp thirdMap fourthMap)) :=
  Eq.trans
    (TraceCorQHom.comp_assoc_four_middle_left_outer_edge
      firstMap
      secondMap
      thirdMap
      fourthMap)
    (TraceCorQHom.comp_assoc_four_tail_edge
      firstMap
      secondMap
      thirdMap
      fourthMap)

/-- Normalize the fourfold composite split as two binary composites. -/
theorem TraceCorQHom.comp_assoc_four_binary
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
  TraceCorQHom.comp_assoc_four_left_inner_edge
    firstMap
    secondMap
    thirdMap
    fourthMap

/-- Normalize the fourfold composite whose right tail is left-associated. -/
theorem TraceCorQHom.comp_assoc_four_middle_right
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
  TraceCorQHom.comp_assoc_four_tail_edge
    firstMap
    secondMap
    thirdMap
    fourthMap

/-- The right-associated fourfold composite is already in normal form. -/
theorem TraceCorQHom.comp_assoc_four_right
    {first second third fourth fifth : TraceCorQObject}
    (firstMap : TraceCorQHom first second)
    (secondMap : TraceCorQHom second third)
    (thirdMap : TraceCorQHom third fourth)
    (fourthMap : TraceCorQHom fourth fifth) :
    TraceCorQHom.comp
      firstMap
      (TraceCorQHom.comp
        secondMap
        (TraceCorQHom.comp thirdMap fourthMap)) =
      TraceCorQHom.comp
        firstMap
        (TraceCorQHom.comp
          secondMap
          (TraceCorQHom.comp thirdMap fourthMap)) :=
  Eq.refl
    (TraceCorQHom.comp
      firstMap
      (TraceCorQHom.comp
        secondMap
        (TraceCorQHom.comp thirdMap fourthMap)))

end AnalyticMotives
end LFunctions
end Boundary
