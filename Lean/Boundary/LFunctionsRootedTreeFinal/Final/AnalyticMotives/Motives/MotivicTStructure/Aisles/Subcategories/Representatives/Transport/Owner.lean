import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Transport.Owner

/-!
# Transport formulas for aisle and coaisle representatives

This file records reflexive pointwise-equality transport formulas for shifted
bounded aisle and coaisle representative objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The reflexive pointwise-equality lift fixes shifted bounded aisle
representatives. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded_liftOfPointwiseEq_refl
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    (TraceAnalyticMotivicTStructure.Aisle.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Aisle.inclusion cut)
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
          cut
          complex
          degree
          degree_le) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        cut
        complex
        degree
        degree_le :=
  rfl

/-- The reflexive pointwise-equality lift fixes shifted bounded coaisle
representatives. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded_liftOfPointwiseEq_refl
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Coaisle.inclusion cut)
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
          cut
          complex
          degree
          cut_le) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        cut
        complex
        degree
        cut_le :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
