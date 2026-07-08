import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Owner

/-!
# The diagonal window and the analytic motivic heart

This file relates the heart at `cut` to the diagonal window `[cut, cut]`.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Heart membership gives diagonal-window membership. -/
theorem TraceAnalyticMotivicTStructure.window_of_heartAt_self
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.heartAt cut object) :
    TraceAnalyticMotivicTStructure.window cut cut object :=
  TraceAnalyticMotivicTStructure.window_intro
    (TraceAnalyticMotivicTStructure.heartAt_coaisle membership)
    (TraceAnalyticMotivicTStructure.heartAt_aisle membership)

/-- Diagonal-window membership gives heart membership. -/
theorem TraceAnalyticMotivicTStructure.heartAt_of_window_self
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.window cut cut object) :
    TraceAnalyticMotivicTStructure.heartAt cut object :=
  TraceAnalyticMotivicTStructure.heartAt_intro
    (TraceAnalyticMotivicTStructure.window_aisle membership)
    (TraceAnalyticMotivicTStructure.window_coaisle membership)

/-- The functor from the heart to the diagonal window. -/
abbrev TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart cut ⥤
      TraceAnalyticMotivicTStructure.Window cut cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.window cut cut)
    (TraceAnalyticMotivicTStructure.Heart.inclusion cut)
    (fun object =>
      TraceAnalyticMotivicTStructure.window_of_heartAt_self
        object.property)

/-- The functor from the diagonal window to the heart. -/
abbrev TraceAnalyticMotivicTStructure.Window.diagonalToHeart
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Window cut cut ⥤
      TraceAnalyticMotivicTStructure.Heart cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.heartAt cut)
    (TraceAnalyticMotivicTStructure.Window.inclusion cut cut)
    (fun object =>
      TraceAnalyticMotivicTStructure.heartAt_of_window_self
        object.property)

/-- Heart to diagonal window preserves the ambient object. -/
theorem TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow cut ⋙
        TraceAnalyticMotivicTStructure.Window.inclusion cut cut =
      TraceAnalyticMotivicTStructure.Heart.inclusion cut :=
  rfl

/-- Diagonal window to heart preserves the ambient object. -/
theorem TraceAnalyticMotivicTStructure.Window.diagonalToHeart_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut ⋙
        TraceAnalyticMotivicTStructure.Heart.inclusion cut =
      TraceAnalyticMotivicTStructure.Window.inclusion cut cut :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
