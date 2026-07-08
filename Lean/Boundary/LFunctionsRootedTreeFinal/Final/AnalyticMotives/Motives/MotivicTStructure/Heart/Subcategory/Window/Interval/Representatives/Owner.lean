import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Owner

/-!
# Representative formulas for heart-to-window interval functors

This file records how exact-degree heart representative objects map into
enclosing interval-window representative objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Sending an exact-degree heart representative into an enclosing interval
window gives the corresponding shifted bounded window representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Heart.toWindow
        lower_le_center
        center_le_upper).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
          complex
          center) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        center
        lower_le_center
        center_le_upper
        complex :=
  rfl

/-- Sending a translated exact-degree heart representative into an enclosing
interval window gives the corresponding shifted bounded window representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow
    {lower degree upper shift : ℤ}
    (lower_le_degree_shift : lower ≤ degree + shift)
    (degree_shift_le_upper : degree + shift ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Heart.toWindow
        lower_le_degree_shift
        degree_shift_le_upper).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        (degree + shift)
        lower_le_degree_shift
        degree_shift_le_upper
        complex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
