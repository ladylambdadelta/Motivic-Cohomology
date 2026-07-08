import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Transport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Transport.Owner

/-!
# Transport formulas for heart-to-window representative objects

This file records that reflexive pointwise-equality transport of the target
window fixes exact-degree heart representative images under `Heart.toWindow`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mapping an exact-degree heart representative into a window and then applying
reflexive pointwise-equality transport gives the same window representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_liftOfPointwiseEq_refl
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
        (fun object => Eq.refl object.object)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          lower_le_center
          center_le_upper).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            center)) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        center
        lower_le_center
        center_le_upper
        complex :=
  rfl

/-- Mapping a translated exact-degree heart representative into a window and
then applying reflexive pointwise-equality transport gives the same window
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_liftOfPointwiseEq_refl
    {lower degree upper shift : ℤ}
    (lower_le_degree_shift : lower ≤ degree + shift)
    (degree_shift_le_upper : degree + shift ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
        (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
        (fun object => Eq.refl object.object)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          lower_le_degree_shift
          degree_shift_le_upper).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        (degree + shift)
        lower_le_degree_shift
        degree_shift_le_upper
        complex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
