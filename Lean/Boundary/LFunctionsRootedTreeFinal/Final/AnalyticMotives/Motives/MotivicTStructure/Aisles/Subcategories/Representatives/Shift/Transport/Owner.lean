import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Shift.Owner

/-!
# Transport formulas for translated aisle and coaisle representatives

This file records reflexive pointwise-equality transport formulas for translated
shifted bounded aisle and coaisle representative objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Reflexive pointwise-equality transport fixes translated aisle
representatives. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight_liftOfPointwiseEq_refl
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    (TraceAnalyticMotivicTStructure.Aisle.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Aisle.inclusion (cut + shift))
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
          cut
          shift
          complex
          degree
          degree_le) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        cut
        shift
        complex
        degree
        degree_le :=
  rfl

/-- Reflexive pointwise-equality transport fixes translated coaisle
representatives. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight_liftOfPointwiseEq_refl
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Coaisle.inclusion (cut + shift))
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
          cut
          shift
          complex
          degree
          cut_le) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        cut
        shift
        complex
        degree
        cut_le :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
