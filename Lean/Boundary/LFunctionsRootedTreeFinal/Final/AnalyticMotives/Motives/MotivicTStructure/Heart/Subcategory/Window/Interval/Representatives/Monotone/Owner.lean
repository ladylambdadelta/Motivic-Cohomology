import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Owner

/-!
# Monotone formulas for heart-to-window representative objects

This file records how exact-degree heart representative objects behave when an
enclosing interval window is widened after applying `Heart.toWindow`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mapping an exact-degree heart representative into an inner window and then
widening the window gives the same window representative constructed directly in
the outer window. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_inclusionOfBounds
    {outerLower innerLower center innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_center : innerLower ≤ center)
    (center_le_innerUpper : center ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
        outerLower_le_innerLower
        innerUpper_le_outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          innerLower_le_center
          center_le_innerUpper).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            center)) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        center
        (le_trans outerLower_le_innerLower innerLower_le_center)
        (le_trans center_le_innerUpper innerUpper_le_outerUpper)
        complex :=
  rfl

/-- Mapping a translated exact-degree heart representative into an inner window
and then widening the window gives the same window representative constructed
directly in the outer window. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_inclusionOfBounds
    {outerLower innerLower degree innerUpper outerUpper shift : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_degree_shift : innerLower ≤ degree + shift)
    (degree_shift_le_innerUpper : degree + shift ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
        outerLower_le_innerLower
        innerUpper_le_outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Heart.toWindow
          innerLower_le_degree_shift
          degree_shift_le_innerUpper).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        (degree + shift)
        (le_trans outerLower_le_innerLower innerLower_le_degree_shift)
        (le_trans degree_shift_le_innerUpper innerUpper_le_outerUpper)
        complex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
