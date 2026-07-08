import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Diagonal.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Projections.Owner

/-!
# Projection formulas for singleton heart-to-window representatives

This file records the aisle and coaisle projections of exact-degree heart
representatives after mapping through the singleton heart-to-window interval.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projecting an exact-degree heart representative after singleton
heart-to-window gives the exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_self_toAisle
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
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting an exact-degree heart representative after singleton
heart-to-window gives the exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_self_toCoaisle
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
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- Projecting a translated exact-degree heart representative after singleton
heart-to-window gives the translated exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_self_toAisle
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

/-- Projecting a translated exact-degree heart representative after singleton
heart-to-window gives the translated exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_self_toCoaisle
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

end AnalyticMotives
end LFunctions
end Boundary
