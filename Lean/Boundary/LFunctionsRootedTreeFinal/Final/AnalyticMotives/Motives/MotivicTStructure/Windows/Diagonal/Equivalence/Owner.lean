import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Diagonal.Projections.Owner

/-!
# Equivalence laws for the diagonal window and the heart

This file records that the concrete functors between the heart at `cut` and
the diagonal window `[cut, cut]` are inverse at the functor level.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Heart to diagonal window and back is the identity functor on the heart. -/
theorem TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow_comp_diagonalToHeart
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow cut ⋙
        TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut =
      𝟭 (TraceAnalyticMotivicTStructure.Heart cut) :=
  rfl

/-- Diagonal window to heart and back is the identity functor on the diagonal
window. -/
theorem TraceAnalyticMotivicTStructure.Window.diagonalToHeart_comp_toDiagonalWindow
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut ⋙
        TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow cut =
      𝟭 (TraceAnalyticMotivicTStructure.Window cut cut) :=
  rfl

/-- The heart-side diagonal round trip preserves the ambient inclusion. -/
theorem TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow_comp_diagonalToHeart_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow cut ⋙
        TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut ⋙
        TraceAnalyticMotivicTStructure.Heart.inclusion cut =
      TraceAnalyticMotivicTStructure.Heart.inclusion cut :=
  rfl

/-- The window-side diagonal round trip preserves the ambient inclusion. -/
theorem TraceAnalyticMotivicTStructure.Window.diagonalToHeart_comp_toDiagonalWindow_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut ⋙
        TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow cut ⋙
        TraceAnalyticMotivicTStructure.Window.inclusion cut cut =
      TraceAnalyticMotivicTStructure.Window.inclusion cut cut :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
