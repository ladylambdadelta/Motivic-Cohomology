import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Shift.Monotone.Owner

/-!
# Ambient projections after monotone inclusions for translated aisle representatives

This file records ambient-object formulas for translated aisle and coaisle
representatives after monotone inclusions of shifted cuts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After monotone inclusion, a translated aisle representative has the
expected ambient stable comparison-source object. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight_inclusionOfLE_object
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le_lower : degree ≤ lower) :
    (TraceAnalyticMotivicTStructure.Aisle.inclusion (upper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Aisle.inclusionOfLE
          (add_le_add_right cut_le shift)).obj
          (TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
            lower
            shift
            complex
            degree
            degree_le_lower)) =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

/-- After monotone inclusion, a translated coaisle representative has the
expected ambient stable comparison-source object. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight_inclusionOfLE_object
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (upper_le_degree : upper ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.inclusion (lower + shift)).obj
        ((TraceAnalyticMotivicTStructure.Coaisle.inclusionOfLE
          (add_le_add_right cut_le shift)).obj
          (TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
            upper
            shift
            complex
            degree
            upper_le_degree)) =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
