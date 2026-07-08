import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.CutTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Monotone.Owner

/-!
# Cut-transport formulas for window representatives

This file records how shifted bounded window representative objects behave
under wider-window cut-transport lifts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A shifted bounded window representative carried by a wider-window
cut-transport lift is the representative constructed directly in the wider
window. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_liftToWiderOfPointwiseEq
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (degree : ℤ)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
        outerLower_le_innerLower
        innerUpper_le_outerUpper
        (TraceAnalyticMotivicTStructure.Window.inclusion
          innerLower
          innerUpper)
        (fun object => Eq.refl object.object)).obj
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

/-- A singleton shifted bounded window representative carried by a wider-window
cut-transport lift is the representative constructed directly in the wider
window. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_liftToWiderOfPointwiseEq
    {outerLower degree outerUpper : ℤ}
    (outerLower_le_degree : outerLower ≤ degree)
    (degree_le_outerUpper : degree ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
        outerLower_le_degree
        degree_le_outerUpper
        (TraceAnalyticMotivicTStructure.Window.inclusion
          degree
          degree)
        (fun object => Eq.refl object.object)).obj
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
