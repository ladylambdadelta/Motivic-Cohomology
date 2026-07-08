import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Homotopy.Shift.Owner

/-!
# Functoriality of analytic trace homotopy shifts

This file records the morphism action of the integer shift functors on the
analytic trace homotopy category and their identity and composition laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The shifted morphism induced by the integer shift functor. -/
def TraceAnalyticHomotopyCategory.shiftedMap
    {source target : TraceAnalyticHomotopyCategory}
    (hom : source ⟶ target)
    (degree : ℤ) :
    TraceAnalyticHomotopyCategory.shiftedObject source degree ⟶
      TraceAnalyticHomotopyCategory.shiftedObject target degree :=
  (TraceAnalyticHomotopyCategory.shiftFunctor degree).map hom

/-- The shifted morphism is the map part of the shift functor. -/
theorem TraceAnalyticHomotopyCategory.shiftedMap_eq
    {source target : TraceAnalyticHomotopyCategory}
    (hom : source ⟶ target)
    (degree : ℤ) :
    TraceAnalyticHomotopyCategory.shiftedMap hom degree =
      (TraceAnalyticHomotopyCategory.shiftFunctor degree).map hom :=
  rfl

/-- Shifting sends identity morphisms to identity morphisms. -/
theorem TraceAnalyticHomotopyCategory.shiftedMap_id
    (motive : TraceAnalyticHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticHomotopyCategory.shiftedMap (𝟙 motive) degree =
      𝟙 (TraceAnalyticHomotopyCategory.shiftedObject motive degree) :=
  (TraceAnalyticHomotopyCategory.shiftFunctor degree).map_id motive

/-- Shifting sends composite morphisms to composite morphisms. -/
theorem TraceAnalyticHomotopyCategory.shiftedMap_comp
    {first second third : TraceAnalyticHomotopyCategory}
    (left : first ⟶ second)
    (right : second ⟶ third)
    (degree : ℤ) :
    TraceAnalyticHomotopyCategory.shiftedMap (left ≫ right) degree =
      TraceAnalyticHomotopyCategory.shiftedMap left degree ≫
        TraceAnalyticHomotopyCategory.shiftedMap right degree :=
  (TraceAnalyticHomotopyCategory.shiftFunctor degree).map_comp left right

end AnalyticMotives
end LFunctions
end Boundary
