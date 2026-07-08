import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Transport.Owner

/-!
# Transport formulas for shifted heart-to-window interval representatives

This file records reflexive pointwise-equality transport normalization for
translated exact-degree heart representatives mapped into translated interval
windows.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mapping a translated exact-degree heart representative into a translated
interval window and then applying reflexive pointwise-equality transport gives
the translated shifted bounded window representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindowAddRight_liftOfPointwiseEq_refl
    {lower degree upper : ℤ}
    (shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
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
            degree)) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
        degree
        shift
        lower_le_degree
        degree_le_upper
        complex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
