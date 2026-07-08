import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Owner

/-!
# Monotone formulas for shifted heart-to-window interval representatives

This file records how translated exact-degree heart representatives behave
when translated enclosing interval windows are widened.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mapping a translated exact-degree heart representative into a translated
inner interval window and then widening the translated window gives the
translated window representative constructed directly in the translated outer
window. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindowAddRight_inclusionOfBounds
    {outerLower innerLower degree innerUpper outerUpper : ℤ}
    (shift : ℤ)
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
        (add_le_add_right outerLower_le_innerLower shift)
        (add_le_add_right innerUpper_le_outerUpper shift)).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          (add_le_add_right innerLower_le_degree shift)
          (add_le_add_right degree_le_innerUpper shift)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
        degree
        shift
        (le_trans outerLower_le_innerLower innerLower_le_degree)
        (le_trans degree_le_innerUpper innerUpper_le_outerUpper)
        complex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
