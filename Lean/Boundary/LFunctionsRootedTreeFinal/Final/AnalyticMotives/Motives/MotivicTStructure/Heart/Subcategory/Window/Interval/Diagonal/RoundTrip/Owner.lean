import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Diagonal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Diagonal.Equivalence.Owner

/-!
# Round-trip laws for singleton heart-to-window interval functors

This file records the diagonal-window-side round trip using the singleton
`Heart.toWindow` interval functor.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Diagonal-window-to-heart followed by singleton heart-to-window is the
identity functor on the diagonal window. -/
theorem TraceAnalyticMotivicTStructure.Window.diagonalToHeart_comp_toWindow_self
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut ⋙
        TraceAnalyticMotivicTStructure.Heart.toWindow
          (lower := cut)
          (center := cut)
          (upper := cut)
          le_rfl
          le_rfl =
      𝟭 (TraceAnalyticMotivicTStructure.Window cut cut) :=
  rfl

/-- The diagonal-window-side singleton round trip preserves the ambient
inclusion. -/
theorem TraceAnalyticMotivicTStructure.Window.diagonalToHeart_comp_toWindow_self_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut ⋙
        TraceAnalyticMotivicTStructure.Heart.toWindow
          (lower := cut)
          (center := cut)
          (upper := cut)
          le_rfl
          le_rfl ⋙
        TraceAnalyticMotivicTStructure.Window.inclusion cut cut =
      TraceAnalyticMotivicTStructure.Window.inclusion cut cut :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
