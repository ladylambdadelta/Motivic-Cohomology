import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Shift.Transport.Owner

/-!
# Ambient projections after transport for translated aisle representatives

This file records ambient-object formulas for translated aisle and coaisle
representatives after reflexive pointwise-equality transport.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After reflexive transport, a translated aisle representative has the
expected ambient stable comparison-source object. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight_liftOfPointwiseEq_refl_object
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    (TraceAnalyticMotivicTStructure.Aisle.inclusion (cut + shift)).obj
        ((TraceAnalyticMotivicTStructure.Aisle.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Aisle.inclusion (cut + shift))
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
            cut
            shift
            complex
            degree
            degree_le)) =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

/-- After reflexive transport, a translated coaisle representative has the
expected ambient stable comparison-source object. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight_liftOfPointwiseEq_refl_object
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.inclusion (cut + shift)).obj
        ((TraceAnalyticMotivicTStructure.Coaisle.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Coaisle.inclusion (cut + shift))
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
            cut
            shift
            complex
            degree
            cut_le)) =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
