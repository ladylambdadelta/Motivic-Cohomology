import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Diagonal.Equivalence.Owner

/-!
# Representative formulas for the diagonal heart-window equivalence

This file records that exact-degree shifted bounded representatives are fixed
by the diagonal heart-window round trips.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- An exact-degree heart representative is fixed by the heart-to-window-to-heart
diagonal round trip. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_diagonalRoundTrip
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow degree ⋙
        TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

/-- A singleton-window representative is fixed by the window-to-heart-to-window
diagonal round trip. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_diagonalRoundTrip
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree ⋙
        TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow degree).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

/-- A translated exact-degree heart representative is fixed by the
heart-to-window-to-heart diagonal round trip. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_diagonalRoundTrip
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow
        (degree + shift) ⋙
        TraceAnalyticMotivicTStructure.Window.diagonalToHeart
          (degree + shift)).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
        shift
        complex
        degree :=
  rfl

/-- A translated singleton-window representative is fixed by the
window-to-heart-to-window diagonal round trip. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_diagonalRoundTrip
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.diagonalToHeart
        (degree + shift) ⋙
        TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow
          (degree + shift)).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
        shift
        complex
        degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
