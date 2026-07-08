import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Transport.Owner

/-!
# Heart-window functors for the analytic motivic t-structure

This file upgrades the concrete heart-window membership theorem to functors
from the heart into enclosing aisle and coaisle subcategories.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A heart object at `center` maps into any enclosing upper aisle. -/
abbrev TraceAnalyticMotivicTStructure.Heart.toUpperAisle
    {center upper : ℤ}
    (center_le_upper : center ≤ upper) :
    TraceAnalyticMotivicTStructure.Heart center ⥤
      TraceAnalyticMotivicTStructure.Aisle upper :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.aisleLE upper)
    (TraceAnalyticMotivicTStructure.Heart.inclusion center)
    (fun object =>
      TraceAnalyticMotivicTStructure.aisleLE_mono
        center_le_upper
        (TraceAnalyticMotivicTStructure.heartAt_aisle object.property))

/-- A heart object at `center` maps into any enclosing lower coaisle. -/
abbrev TraceAnalyticMotivicTStructure.Heart.toLowerCoaisle
    {lower center : ℤ}
    (lower_le_center : lower ≤ center) :
    TraceAnalyticMotivicTStructure.Heart center ⥤
      TraceAnalyticMotivicTStructure.Coaisle lower :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.coaisleGE lower)
    (TraceAnalyticMotivicTStructure.Heart.inclusion center)
    (fun object =>
      TraceAnalyticMotivicTStructure.coaisleGE_mono
        lower_le_center
        (TraceAnalyticMotivicTStructure.heartAt_coaisle object.property))

/-- The upper-aisle heart-window functor preserves ambient objects. -/
theorem TraceAnalyticMotivicTStructure.Heart.toUpperAisle_comp_inclusion
    {center upper : ℤ}
    (center_le_upper : center ≤ upper) :
    TraceAnalyticMotivicTStructure.Heart.toUpperAisle center_le_upper ⋙
        TraceAnalyticMotivicTStructure.Aisle.inclusion upper =
      TraceAnalyticMotivicTStructure.Heart.inclusion center :=
  rfl

/-- The lower-coaisle heart-window functor preserves ambient objects. -/
theorem TraceAnalyticMotivicTStructure.Heart.toLowerCoaisle_comp_inclusion
    {lower center : ℤ}
    (lower_le_center : lower ≤ center) :
    TraceAnalyticMotivicTStructure.Heart.toLowerCoaisle lower_le_center ⋙
        TraceAnalyticMotivicTStructure.Coaisle.inclusion lower =
      TraceAnalyticMotivicTStructure.Heart.inclusion center :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
