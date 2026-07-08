import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Owner

/-!
# Monotone formulas for aisle and coaisle representatives

This file records how shifted bounded representative objects behave under
monotone inclusions of aisle and coaisle full subcategories.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Including a shifted bounded aisle representative into a larger aisle gives
the same representative constructed at the larger cut. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded_inclusionOfLE
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le_lower : degree ≤ lower) :
    (TraceAnalyticMotivicTStructure.Aisle.inclusionOfLE cut_le).obj
        (TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
          lower
          complex
          degree
          degree_le_lower) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        upper
        complex
        degree
        (le_trans degree_le_lower cut_le) :=
  rfl

/-- Including a shifted bounded coaisle representative into a lower coaisle
gives the same representative constructed at the lower cut. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded_inclusionOfLE
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (upper_le_degree : upper ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.inclusionOfLE cut_le).obj
        (TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
          upper
          complex
          degree
          upper_le_degree) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        lower
        complex
        degree
        (le_trans cut_le upper_le_degree) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
