import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Owner

/-!
# Projection formulas for heart-to-window representative objects

This file records the aisle and coaisle projections of exact-degree heart
representatives after mapping them into enclosing interval windows.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Sending an exact-degree heart representative into an enclosing window and
then projecting to the upper aisle gives the corresponding aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_toAisle
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          lower_le_center
          center_le_upper).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            center)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        upper
        complex
        center
        center_le_upper :=
  rfl

/-- Sending an exact-degree heart representative into an enclosing window and
then projecting to the lower coaisle gives the corresponding coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_toCoaisle
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          lower_le_center
          center_le_upper).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            center)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        lower
        complex
        center
        lower_le_center :=
  rfl

/-- Sending a translated exact-degree heart representative into an enclosing
window and then projecting to the upper aisle gives the corresponding aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_toAisle
    {lower degree upper shift : ℤ}
    (lower_le_degree_shift : lower ≤ degree + shift)
    (degree_shift_le_upper : degree + shift ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          lower_le_degree_shift
          degree_shift_le_upper).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        upper
        complex
        (degree + shift)
        degree_shift_le_upper :=
  rfl

/-- Sending a translated exact-degree heart representative into an enclosing
window and then projecting to the lower coaisle gives the corresponding
coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_toCoaisle
    {lower degree upper shift : ℤ}
    (lower_le_degree_shift : lower ≤ degree + shift)
    (degree_shift_le_upper : degree + shift ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          lower_le_degree_shift
          degree_shift_le_upper).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        lower
        complex
        (degree + shift)
        lower_le_degree_shift :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
