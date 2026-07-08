import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Owner

/-!
# Shift formulas for heart-to-window interval representatives

This file records how translated exact-degree heart representatives map into
translated interval-window representative objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Sending a translated exact-degree heart representative into a translated
enclosing interval window gives the translated shifted bounded window
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindowAddRight
    {lower degree upper : ℤ}
    (shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Heart.toWindow
        (add_le_add_right lower_le_degree shift)
        (add_le_add_right degree_le_upper shift)).obj
        (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
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
