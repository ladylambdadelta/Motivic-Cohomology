import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Transport.Owner

/-!
# Projection formulas after transport for heart-to-window representatives

This file records the aisle and coaisle projections of exact-degree heart
representative images after reflexive target-window transport.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After reflexive target-window transport, projecting an exact-degree
heart-to-window representative image to the upper aisle gives the corresponding
aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_liftOfPointwiseEq_refl_toAisle
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
          (fun object => Eq.refl object.object)).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            lower_le_center
            center_le_upper).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
              complex
              center))) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        upper
        complex
        center
        center_le_upper :=
  rfl

/-- After reflexive target-window transport, projecting an exact-degree
heart-to-window representative image to the lower coaisle gives the
corresponding coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_liftOfPointwiseEq_refl_toCoaisle
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
          (fun object => Eq.refl object.object)).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            lower_le_center
            center_le_upper).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
              complex
              center))) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        lower
        complex
        center
        lower_le_center :=
  rfl

/-- After reflexive target-window transport, projecting a translated
heart-to-window representative image to the upper aisle gives the corresponding
aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_liftOfPointwiseEq_refl_toAisle
    {lower degree upper shift : ℤ}
    (lower_le_degree_shift : lower ≤ degree + shift)
    (degree_shift_le_upper : degree + shift ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
          (fun object => Eq.refl object.object)).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            lower_le_degree_shift
            degree_shift_le_upper).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        upper
        complex
        (degree + shift)
        degree_shift_le_upper :=
  rfl

/-- After reflexive target-window transport, projecting a translated
heart-to-window representative image to the lower coaisle gives the
corresponding coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_liftOfPointwiseEq_refl_toCoaisle
    {lower degree upper shift : ℤ}
    (lower_le_degree_shift : lower ≤ degree + shift)
    (degree_shift_le_upper : degree + shift ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle lower upper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
          (fun object => Eq.refl object.object)).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            lower_le_degree_shift
            degree_shift_le_upper).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        lower
        complex
        (degree + shift)
        lower_le_degree_shift :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
