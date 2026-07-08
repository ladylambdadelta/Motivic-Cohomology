import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Shift.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Shift.Transport.Owner

/-!
# Projection formulas after shifted heart-to-window transport

This file records the aisle and coaisle projections of translated
exact-degree heart representatives after mapping them into translated interval
windows and then applying reflexive pointwise-equality transport.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After reflexive target-window transport, projecting the translated
heart-to-window representative image to the upper aisle gives the translated
shifted bounded aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindowAddRight_liftOfPointwiseEq_refl_toAisle
    {lower degree upper : ℤ}
    (shift : ℤ)
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
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            (add_le_add_right lower_le_degree shift)
            (add_le_add_right degree_le_upper shift)).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        upper
        shift
        complex
        degree
        degree_le_upper :=
  rfl

/-- After reflexive target-window transport, projecting the translated
heart-to-window representative image to the lower coaisle gives the translated
shifted bounded coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindowAddRight_liftOfPointwiseEq_refl_toCoaisle
    {lower degree upper : ℤ}
    (shift : ℤ)
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
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            (add_le_add_right lower_le_degree shift)
            (add_le_add_right degree_le_upper shift)).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        lower
        shift
        complex
        degree
        lower_le_degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
