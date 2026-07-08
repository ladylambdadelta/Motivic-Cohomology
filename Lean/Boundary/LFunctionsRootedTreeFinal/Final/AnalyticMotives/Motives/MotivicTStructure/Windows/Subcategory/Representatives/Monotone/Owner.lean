import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Owner

/-!
# Monotone formulas for window representatives

This file records how shifted bounded window representative objects behave
under inclusions into wider windows.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Including a shifted bounded window representative into a wider window gives
the same representative constructed directly in the wider window. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_inclusionOfBounds
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (degree : ℤ)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
        outerLower_le_innerLower
        innerUpper_le_outerUpper).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
          degree
          innerLower_le_degree
          degree_le_innerUpper
          complex) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        degree
        (le_trans outerLower_le_innerLower innerLower_le_degree)
        (le_trans degree_le_innerUpper innerUpper_le_outerUpper)
        complex :=
  rfl

/-- Including a singleton shifted bounded window representative into a wider
window gives the same representative constructed directly in the wider window. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_inclusionOfBounds
    {outerLower degree outerUpper : ℤ}
    (outerLower_le_degree : outerLower ≤ degree)
    (degree_le_outerUpper : degree ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
        outerLower_le_degree
        degree_le_outerUpper).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        degree
        outerLower_le_degree
        degree_le_outerUpper
        complex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
