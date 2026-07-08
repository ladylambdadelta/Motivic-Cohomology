import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Diagonal.Owner

/-!
# Projection compatibilities for the diagonal window

This file records how the heart/diagonal-window bridge interacts with aisle and
coaisle projections.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Heart membership is equivalent to diagonal-window membership. -/
theorem TraceAnalyticMotivicTStructure.heartAt_iff_window_self
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticMotivicTStructure.heartAt cut object ↔
      TraceAnalyticMotivicTStructure.window cut cut object :=
  Iff.intro
    (fun membership =>
      TraceAnalyticMotivicTStructure.window_of_heartAt_self
        membership)
    (fun membership =>
      TraceAnalyticMotivicTStructure.heartAt_of_window_self
        membership)

/-- Heart to diagonal-window followed by the upper-aisle projection is the
heart-to-aisle projection. -/
theorem TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow_comp_toAisle
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow cut ⋙
        TraceAnalyticMotivicTStructure.Window.toAisle cut cut =
      TraceAnalyticMotivicTStructure.Heart.toAisle cut :=
  rfl

/-- Heart to diagonal-window followed by the lower-coaisle projection is the
heart-to-coaisle projection. -/
theorem TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow_comp_toCoaisle
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow cut ⋙
        TraceAnalyticMotivicTStructure.Window.toCoaisle cut cut =
      TraceAnalyticMotivicTStructure.Heart.toCoaisle cut :=
  rfl

/-- Diagonal-window to heart followed by heart-to-aisle is the window's
upper-aisle projection. -/
theorem TraceAnalyticMotivicTStructure.Window.diagonalToHeart_comp_toAisle
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut ⋙
        TraceAnalyticMotivicTStructure.Heart.toAisle cut =
      TraceAnalyticMotivicTStructure.Window.toAisle cut cut :=
  rfl

/-- Diagonal-window to heart followed by heart-to-coaisle is the window's
lower-coaisle projection. -/
theorem TraceAnalyticMotivicTStructure.Window.diagonalToHeart_comp_toCoaisle
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut ⋙
        TraceAnalyticMotivicTStructure.Heart.toCoaisle cut =
      TraceAnalyticMotivicTStructure.Window.toCoaisle cut cut :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
