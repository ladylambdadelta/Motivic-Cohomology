import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Full.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Associativity.Full.Edges.Owner

/-!
# Public fourfold associativity for typed trace correspondences

This file exposes the full fourfold reassociation normal forms for typed
Q-linear trace correspondences at the top root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root normalizes the fully left-associated fourfold composite. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_assoc_four_left
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
  TraceCorQHom.comp_assoc_four_left
    firstMap
    secondMap
    thirdMap
    fourthMap

/-- The top root normalizes the fourfold composite with the middle pair first. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_assoc_four_middle_left
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
  TraceCorQHom.comp_assoc_four_middle_left
    firstMap
    secondMap
    thirdMap
    fourthMap

/-- The top root normalizes the fourfold composite split into two binary composites. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_assoc_four_binary
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
  TraceCorQHom.comp_assoc_four_binary
    firstMap
    secondMap
    thirdMap
    fourthMap

/-- The top root normalizes the fourfold composite with a left-associated right tail. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_assoc_four_middle_right
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
  TraceCorQHom.comp_assoc_four_middle_right
    firstMap
    secondMap
    thirdMap
    fourthMap

/-- The top root exposes that the right-associated fourfold composite is normal. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_assoc_four_right
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
  TraceCorQHom.comp_assoc_four_right
    firstMap
    secondMap
    thirdMap
    fourthMap

end AnalyticMotives
end LFunctions
end Boundary
