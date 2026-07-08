import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.CutTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Monotone.Owner

/-!
# Cut-transport formulas for aisle and coaisle representatives

This file records how shifted bounded aisle and coaisle representative objects
behave under cut-transport lifts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A shifted bounded aisle representative carried by cut transport to a larger
aisle is the representative constructed directly at the larger cut. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded_liftToLargerOfPointwiseEq
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le_lower : degree ≤ lower) :
    (TraceAnalyticMotivicTStructure.Aisle.liftToLargerOfPointwiseEq
        cut_le
        (TraceAnalyticMotivicTStructure.Aisle.inclusion lower)
        (fun object => Eq.refl object.object)).obj
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

/-- A shifted bounded coaisle representative carried by cut transport to a
lower coaisle is the representative constructed directly at the lower cut. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded_liftToLowerOfPointwiseEq
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (upper_le_degree : upper ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.liftToLowerOfPointwiseEq
        cut_le
        (TraceAnalyticMotivicTStructure.Coaisle.inclusion upper)
        (fun object => Eq.refl object.object)).obj
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
