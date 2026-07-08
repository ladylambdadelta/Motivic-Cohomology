import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Shift.Owner

/-!
# Monotone formulas for translated aisle and coaisle representatives

This file records how translated shifted bounded aisle and coaisle
representative objects behave under monotone inclusions of shifted cuts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Including a translated shifted bounded aisle representative into a larger
translated aisle gives the same representative constructed at the larger
translated cut. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight_inclusionOfLE
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le_lower : degree ≤ lower) :
    (TraceAnalyticMotivicTStructure.Aisle.inclusionOfLE
        (add_le_add_right cut_le shift)).obj
        (TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
          lower
          shift
          complex
          degree
          degree_le_lower) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        upper
        shift
        complex
        degree
        (le_trans degree_le_lower cut_le) :=
  rfl

/-- Including a translated shifted bounded coaisle representative into a lower
translated coaisle gives the same representative constructed at the lower
translated cut. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight_inclusionOfLE
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (upper_le_degree : upper ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.inclusionOfLE
        (add_le_add_right cut_le shift)).obj
        (TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
          upper
          shift
          complex
          degree
          upper_le_degree) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        lower
        shift
        complex
        degree
        (le_trans cut_le upper_le_degree) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
