import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Diagonal.Representatives.RoundTrip.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Projections.Owner

/-!
# Projection formulas after singleton window-side round trips

This file records the aisle and coaisle projections of singleton-window
representatives after the diagonal-window-to-heart-to-singleton-window round
trip.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projecting a singleton-window representative after the window-side singleton
round trip gives the exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_diagonalToHeart_toWindow_self_toAisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toAisle degree degree).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          (lower := degree)
          (center := degree)
          (upper := degree)
          le_rfl
          le_rfl).obj
          ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
            (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a singleton-window representative after the window-side singleton
round trip gives the exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_diagonalToHeart_toWindow_self_toCoaisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle degree degree).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          (lower := degree)
          (center := degree)
          (upper := degree)
          le_rfl
          le_rfl).obj
          ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
            (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a translated singleton-window representative after the
window-side singleton round trip gives the translated exact-degree aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_diagonalToHeart_toWindow_self_toAisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        (degree + shift)
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          (lower := degree + shift)
          (center := degree + shift)
          (upper := degree + shift)
          le_rfl
          le_rfl).obj
          ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart
            (degree + shift)).obj
            (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        degree
        shift
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a translated singleton-window representative after the
window-side singleton round trip gives the translated exact-degree coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_diagonalToHeart_toWindow_self_toCoaisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        (degree + shift)
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          (lower := degree + shift)
          (center := degree + shift)
          (upper := degree + shift)
          le_rfl
          le_rfl).obj
          ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart
            (degree + shift)).obj
            (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        degree
        shift
        complex
        degree
        le_rfl :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
