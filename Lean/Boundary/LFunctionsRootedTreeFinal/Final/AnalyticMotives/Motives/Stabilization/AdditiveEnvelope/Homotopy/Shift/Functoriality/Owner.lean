import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Shift.Owner

/-!
# Functoriality of additive analytic homotopy shifts

This file records the morphism action of integer shift functors in the
additive analytic homotopy category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The shifted morphism induced by the additive analytic homotopy shift functor. -/
def TraceAnalyticAdditiveHomotopyCategory.shiftedMap
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedObject source degree ⟶
      TraceAnalyticAdditiveHomotopyCategory.shiftedObject target degree :=
  (TraceAnalyticAdditiveHomotopyCategory.shiftFunctor degree).map hom

/-- The shifted morphism is the map part of the additive homotopy shift functor. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedMap_eq
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedMap hom degree =
      (TraceAnalyticAdditiveHomotopyCategory.shiftFunctor degree).map hom :=
  rfl

/-- Shifting sends additive homotopy identity morphisms to identity morphisms. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedMap_id
    (motive : TraceAnalyticAdditiveHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedMap (𝟙 motive) degree =
      𝟙 (TraceAnalyticAdditiveHomotopyCategory.shiftedObject motive degree) :=
  (TraceAnalyticAdditiveHomotopyCategory.shiftFunctor degree).map_id motive

/-- Shifting sends additive homotopy composite morphisms to composite morphisms. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedMap_comp
    {first second third : TraceAnalyticAdditiveHomotopyCategory}
    (left : first ⟶ second)
    (right : second ⟶ third)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedMap (left ≫ right) degree =
      TraceAnalyticAdditiveHomotopyCategory.shiftedMap left degree ≫
        TraceAnalyticAdditiveHomotopyCategory.shiftedMap right degree :=
  (TraceAnalyticAdditiveHomotopyCategory.shiftFunctor degree).map_comp left right

end AnalyticMotives
end LFunctions
end Boundary
