import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Diagonal.Owner

/-!
# Diagonal specialization of heart-to-window interval functors

This file identifies the general heart-to-window interval functor with the
diagonal-window functor when the interval is `[cut, cut]`.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The general heart-to-window functor for the singleton interval is the
heart-to-diagonal-window functor. -/
theorem TraceAnalyticMotivicTStructure.Heart.toWindow_self_eq_toDiagonalWindow
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart.toWindow
        (lower := cut)
        (center := cut)
        (upper := cut)
        le_rfl
        le_rfl =
      TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow cut :=
  rfl

/-- The singleton heart-to-window functor followed by diagonal-window-to-heart
is the identity on the heart. -/
theorem TraceAnalyticMotivicTStructure.Heart.toWindow_self_comp_diagonalToHeart
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart.toWindow
        (lower := cut)
        (center := cut)
        (upper := cut)
        le_rfl
        le_rfl ⋙
        TraceAnalyticMotivicTStructure.Window.diagonalToHeart cut =
      𝟭 (TraceAnalyticMotivicTStructure.Heart cut) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
