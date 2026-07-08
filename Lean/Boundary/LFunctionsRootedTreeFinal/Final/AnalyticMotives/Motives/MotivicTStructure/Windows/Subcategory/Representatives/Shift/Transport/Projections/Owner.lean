import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Transport.Owner

/-!
# Projection formulas after transport for translated window representatives

This file records the aisle and coaisle projections of translated shifted
bounded window representatives after reflexive pointwise-equality transport.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After reflexive transport, projecting a translated shifted bounded window
representative to its upper aisle gives the translated shifted bounded aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight_liftOfPointwiseEq_refl_toAisle
    {lower upper : ℤ}
    (degree shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        (lower + shift)
        (upper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion
            (lower + shift)
            (upper + shift))
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
            degree
            shift
            lower_le_degree
            degree_le_upper
            complex)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        upper
        shift
        complex
        degree
        degree_le_upper :=
  rfl

/-- After reflexive transport, projecting a translated shifted bounded window
representative to its lower coaisle gives the translated shifted bounded
coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight_liftOfPointwiseEq_refl_toCoaisle
    {lower upper : ℤ}
    (degree shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        (lower + shift)
        (upper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion
            (lower + shift)
            (upper + shift))
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
            degree
            shift
            lower_le_degree
            degree_le_upper
            complex)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        lower
        shift
        complex
        degree
        lower_le_degree :=
  rfl

/-- After reflexive transport, projecting a translated singleton-window
representative to its aisle gives the translated exact-degree aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_liftOfPointwiseEq_refl_toAisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        (degree + shift)
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion
            (degree + shift)
            (degree + shift))
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        degree
        shift
        complex
        degree
        le_rfl :=
  rfl

/-- After reflexive transport, projecting a translated singleton-window
representative to its coaisle gives the translated exact-degree coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_liftOfPointwiseEq_refl_toCoaisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        (degree + shift)
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion
            (degree + shift)
            (degree + shift))
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        degree
        shift
        complex
        degree
        le_rfl :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
