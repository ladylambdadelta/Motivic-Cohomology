import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Projections.Owner

/-!
# Projection formulas for shifted heart-to-window interval representatives

This file records the aisle and coaisle projections of translated exact-degree
heart representatives after mapping them into translated interval windows.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projecting the translated interval-window image of a translated
exact-degree heart representative to its upper aisle gives the translated
shifted bounded aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindowAddRight_toAisle
    {lower degree upper : ℤ}
    (shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        (lower + shift)
        (upper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          (add_le_add_right lower_le_degree shift)
          (add_le_add_right degree_le_upper shift)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        upper
        shift
        complex
        degree
        degree_le_upper :=
  rfl

/-- Projecting the translated interval-window image of a translated
exact-degree heart representative to its lower coaisle gives the translated
shifted bounded coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindowAddRight_toCoaisle
    {lower degree upper : ℤ}
    (shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        (lower + shift)
        (upper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          (add_le_add_right lower_le_degree shift)
          (add_le_add_right degree_le_upper shift)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        lower
        shift
        complex
        degree
        lower_le_degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
