import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Shift.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Diagonal.Representatives.RoundTrip.Owner

/-!
# Heart projection formulas after singleton heart-side round trips

This file records the aisle and coaisle projections of exact-degree heart
representatives after singleton heart-to-window followed by
diagonal-window-to-heart.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projecting an exact-degree heart representative after the heart-side
singleton round trip gives the exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_self_diagonalToHeart_toAisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toAisle degree).obj
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            (lower := degree)
            (center := degree)
            (upper := degree)
            le_rfl
            le_rfl).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting an exact-degree heart representative after the heart-side
singleton round trip gives the exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_self_diagonalToHeart_toCoaisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisle degree).obj
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            (lower := degree)
            (center := degree)
            (upper := degree)
            le_rfl
            le_rfl).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a translated exact-degree heart representative after the
heart-side singleton round trip gives the translated exact-degree aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_self_diagonalToHeart_toAisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toAisle
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart
          (degree + shift)).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            (lower := degree + shift)
            (center := degree + shift)
            (upper := degree + shift)
            le_rfl
            le_rfl).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
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

/-- Projecting a translated exact-degree heart representative after the
heart-side singleton round trip gives the translated exact-degree coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_self_diagonalToHeart_toCoaisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisle
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart
          (degree + shift)).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            (lower := degree + shift)
            (center := degree + shift)
            (upper := degree + shift)
            le_rfl
            le_rfl).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
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
