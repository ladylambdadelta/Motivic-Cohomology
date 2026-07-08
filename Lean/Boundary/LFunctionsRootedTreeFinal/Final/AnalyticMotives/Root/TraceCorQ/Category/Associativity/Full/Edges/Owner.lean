import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Full.Edges.Owner

/-!
# Public fourfold associativity edges for typed trace correspondences

This file exposes the elementary fourfold reassociation edges for typed
Q-linear trace correspondences at the top root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the outer edge from the fully left-associated composite. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_assoc_four_left_outer_edge
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
  TraceCorQHom.comp_assoc_four_left_outer_edge
    firstMap
    secondMap
    thirdMap
    fourthMap

/-- The top root exposes the inner edge from a binary-split fourfold composite. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_assoc_four_left_inner_edge
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

/-- The top root exposes the outer edge from the middle-pair composite. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_assoc_four_middle_left_outer_edge
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
  TraceCorQHom.comp_assoc_four_middle_left_outer_edge
    firstMap
    secondMap
    thirdMap
    fourthMap

/-- The top root exposes the right-tail reassociation edge. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_assoc_four_tail_edge
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

end AnalyticMotives
end LFunctions
end Boundary
