import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Shift.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Transport.Owner

/-!
# Projection formulas after transport for heart representatives

This file records the aisle and coaisle projections of exact-degree heart
representatives after reflexive pointwise-equality transport.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After reflexive heart transport, projecting an exact-degree heart
representative to the aisle gives the exact-degree aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_liftOfPointwiseEq_refl_toAisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toAisle degree).obj
        ((TraceAnalyticMotivicTStructure.Heart.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Heart.inclusion degree)
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- After reflexive heart transport, projecting an exact-degree heart
representative to the coaisle gives the exact-degree coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_liftOfPointwiseEq_refl_toCoaisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisle degree).obj
        ((TraceAnalyticMotivicTStructure.Heart.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Heart.inclusion degree)
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        degree
        complex
        degree
        le_rfl :=
  rfl

/-- After reflexive heart transport, projecting a translated exact-degree heart
representative to the aisle gives the translated exact-degree aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_liftOfPointwiseEq_refl_toAisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toAisle
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Heart.inclusion (degree + shift))
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
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

/-- After reflexive heart transport, projecting a translated exact-degree heart
representative to the coaisle gives the translated exact-degree coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_liftOfPointwiseEq_refl_toCoaisle
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisle
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Heart.inclusion (degree + shift))
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
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
