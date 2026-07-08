import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.DiagonalEquivalence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Shift.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Projections.Owner

/-!
# Projection formulas after diagonal heart-window round trips

This file records aisle and coaisle projections of exact-degree representatives
after the direct diagonal heart-window round trips.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projecting an exact-degree heart representative after the direct diagonal
heart round trip gives the exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_diagonalRoundTrip_toAisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toAisle degree).obj
        ((TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow degree ⋙
          TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting an exact-degree heart representative after the direct diagonal
heart round trip gives the exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_diagonalRoundTrip_toCoaisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisle degree).obj
        ((TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow degree ⋙
          TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a singleton-window representative after the direct diagonal
window round trip gives the exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_diagonalRoundTrip_toAisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toAisle degree degree).obj
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree ⋙
          TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow degree).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a singleton-window representative after the direct diagonal
window round trip gives the exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_diagonalRoundTrip_toCoaisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle degree degree).obj
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart degree ⋙
          TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow degree).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a translated exact-degree heart representative after the direct
diagonal heart round trip gives the translated exact-degree aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_diagonalRoundTrip_toAisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toAisle
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow
          (degree + shift) ⋙
          TraceAnalyticMotivicTStructure.Window.diagonalToHeart
            (degree + shift)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        degree
        shift
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a translated exact-degree heart representative after the direct
diagonal heart round trip gives the translated exact-degree coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_diagonalRoundTrip_toCoaisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisle
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow
          (degree + shift) ⋙
          TraceAnalyticMotivicTStructure.Window.diagonalToHeart
            (degree + shift)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        degree
        shift
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a translated singleton-window representative after the direct
diagonal window round trip gives the translated exact-degree aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_diagonalRoundTrip_toAisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        (degree + shift)
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart
          (degree + shift) ⋙
          TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow
            (degree + shift)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        degree
        shift
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a translated singleton-window representative after the direct
diagonal window round trip gives the translated exact-degree coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_diagonalRoundTrip_toCoaisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        (degree + shift)
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.diagonalToHeart
          (degree + shift) ⋙
          TraceAnalyticMotivicTStructure.Heart.toDiagonalWindow
            (degree + shift)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
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
