import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.CutTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Owner

/-!
# Cut-transport formulas for translated window representatives

This file records how translated shifted bounded window representative objects
behave under wider-window cut-transport lifts of translated bounds.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A translated shifted bounded window representative carried by translated
wider-window cut transport is the translated representative constructed
directly in the wider window. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight_liftToWiderOfPointwiseEq
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (degree shift : ℤ)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
        (add_le_add_right outerLower_le_innerLower shift)
        (add_le_add_right innerUpper_le_outerUpper shift)
        (TraceAnalyticMotivicTStructure.Window.inclusion
          (innerLower + shift)
          (innerUpper + shift))
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
          degree
          shift
          innerLower_le_degree
          degree_le_innerUpper
          complex) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
        degree
        shift
        (le_trans outerLower_le_innerLower innerLower_le_degree)
        (le_trans degree_le_innerUpper innerUpper_le_outerUpper)
        complex :=
  rfl

/-- A translated singleton shifted bounded window representative carried by
translated wider-window cut transport is the translated representative
constructed directly in the wider window. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_liftToWiderOfPointwiseEq
    {outerLower degree outerUpper : ℤ}
    (outerLower_le_degree : outerLower ≤ degree)
    (degree_le_outerUpper : degree ≤ outerUpper)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
        (add_le_add_right outerLower_le_degree shift)
        (add_le_add_right degree_le_outerUpper shift)
        (TraceAnalyticMotivicTStructure.Window.inclusion
          (degree + shift)
          (degree + shift))
        (fun object => Eq.refl object.object)).obj
        (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree) =
      TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
        degree
        shift
        outerLower_le_degree
        degree_le_outerUpper
        complex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
