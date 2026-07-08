import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Transport.Owner

/-!
# Projection formulas after transport for window representatives

This file records the aisle and coaisle projections of shifted bounded window
representatives after reflexive pointwise-equality transport.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After reflexive transport, projecting a shifted bounded window
representative to its upper aisle gives the shifted bounded aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_liftOfPointwiseEq_refl_toAisle
    {lower upper : ℤ}
    (degree : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
            degree
            lower_le_degree
            degree_le_upper
            complex)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        upper
        complex
        degree
        degree_le_upper :=
  rfl

/-- After reflexive transport, projecting a shifted bounded window
representative to its lower coaisle gives the shifted bounded coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_liftOfPointwiseEq_refl_toCoaisle
    {lower upper : ℤ}
    (degree : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
            degree
            lower_le_degree
            degree_le_upper
            complex)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        lower
        complex
        degree
        lower_le_degree :=
  rfl

/-- After reflexive transport, projecting a singleton shifted bounded window
representative to its aisle gives the exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_liftOfPointwiseEq_refl_toAisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toAisle degree degree).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion degree degree)
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- After reflexive transport, projecting a singleton shifted bounded window
representative to its coaisle gives the exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_liftOfPointwiseEq_refl_toCoaisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle degree degree).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion degree degree)
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
