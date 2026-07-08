import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Owner

/-!
# Heart-to-window functors for enclosing intervals

This file upgrades the concrete heart-to-window membership theorem to a functor
from a heart subcategory into every enclosing interval window.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A heart object at `center` maps into every enclosing interval window. -/
abbrev TraceAnalyticMotivicTStructure.Heart.toWindow
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper) :
    TraceAnalyticMotivicTStructure.Heart center ⥤
      TraceAnalyticMotivicTStructure.Window lower upper :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.window lower upper)
    (TraceAnalyticMotivicTStructure.Heart.inclusion center)
    (fun object =>
      TraceAnalyticMotivicTStructure.window_of_heartAt
        lower_le_center
        center_le_upper
        object.property)

/-- Heart-to-window followed by window inclusion is the heart inclusion. -/
theorem TraceAnalyticMotivicTStructure.Heart.toWindow_comp_inclusion
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper) :
    TraceAnalyticMotivicTStructure.Heart.toWindow
        lower_le_center
        center_le_upper ⋙
        TraceAnalyticMotivicTStructure.Window.inclusion lower upper =
      TraceAnalyticMotivicTStructure.Heart.inclusion center :=
  rfl

/-- Heart-to-window followed by the upper-aisle projection is the existing
heart-to-upper-aisle functor. -/
theorem TraceAnalyticMotivicTStructure.Heart.toWindow_comp_toAisle
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper) :
    TraceAnalyticMotivicTStructure.Heart.toWindow
        lower_le_center
        center_le_upper ⋙
        TraceAnalyticMotivicTStructure.Window.toAisle lower upper =
      TraceAnalyticMotivicTStructure.Heart.toUpperAisle center_le_upper :=
  rfl

/-- Heart-to-window followed by the lower-coaisle projection is the existing
heart-to-lower-coaisle functor. -/
theorem TraceAnalyticMotivicTStructure.Heart.toWindow_comp_toCoaisle
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper) :
    TraceAnalyticMotivicTStructure.Heart.toWindow
        lower_le_center
        center_le_upper ⋙
        TraceAnalyticMotivicTStructure.Window.toCoaisle lower upper =
      TraceAnalyticMotivicTStructure.Heart.toLowerCoaisle lower_le_center :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
