import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.CutTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Shift.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Shift.Transport.Owner

/-!
# Cut-transport formulas for translated aisle and coaisle representatives

This file records how translated shifted bounded aisle and coaisle
representative objects behave under cut-transport lifts of shifted cuts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A translated aisle representative carried by cut transport to a larger
translated aisle is the translated representative constructed directly at the
larger cut. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight_liftToLargerOfPointwiseEq
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le_lower : degree ≤ lower) :
    (TraceAnalyticMotivicTStructure.Aisle.liftToLargerOfPointwiseEq
        (add_le_add_right cut_le shift)
        (TraceAnalyticMotivicTStructure.Aisle.inclusion (lower + shift))
        (fun object => Eq.refl object.object)).obj
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

/-- A translated coaisle representative carried by cut transport to a lower
translated coaisle is the translated representative constructed directly at the
lower cut. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight_liftToLowerOfPointwiseEq
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (upper_le_degree : upper ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.liftToLowerOfPointwiseEq
        (add_le_add_right cut_le shift)
        (TraceAnalyticMotivicTStructure.Coaisle.inclusion (upper + shift))
        (fun object => Eq.refl object.object)).obj
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
