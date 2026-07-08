import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.CutTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Projections.Owner

/-!
# Projection formulas after cut transport for window representatives

This file records the aisle and coaisle projections of shifted bounded window
representatives after wider-window cut-transport lifts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After wider-window cut transport, projecting a shifted bounded window
representative to the outer upper aisle gives the shifted bounded aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_liftToWiderOfPointwiseEq_toAisle
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (degree : ℤ)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        outerLower
        outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
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
            complex)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        outerUpper
        complex
        degree
        (le_trans degree_le_innerUpper innerUpper_le_outerUpper) :=
  rfl

/-- After wider-window cut transport, projecting a shifted bounded window
representative to the outer lower coaisle gives the shifted bounded coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_liftToWiderOfPointwiseEq_toCoaisle
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (degree : ℤ)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        outerLower
        outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
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
            complex)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        outerLower
        complex
        degree
        (le_trans outerLower_le_innerLower innerLower_le_degree) :=
  rfl

/-- After wider-window cut transport, projecting a singleton shifted bounded
window representative to the outer upper aisle gives the shifted bounded aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_liftToWiderOfPointwiseEq_toAisle
    {outerLower degree outerUpper : ℤ}
    (outerLower_le_degree : outerLower ≤ degree)
    (degree_le_outerUpper : degree ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        outerLower
        outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
          outerLower_le_degree
          degree_le_outerUpper
          (TraceAnalyticMotivicTStructure.Window.inclusion
            degree
            degree)
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        outerUpper
        complex
        degree
        degree_le_outerUpper :=
  rfl

/-- After wider-window cut transport, projecting a singleton shifted bounded
window representative to the outer lower coaisle gives the shifted bounded
coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_liftToWiderOfPointwiseEq_toCoaisle
    {outerLower degree outerUpper : ℤ}
    (outerLower_le_degree : outerLower ≤ degree)
    (degree_le_outerUpper : degree ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        outerLower
        outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
          outerLower_le_degree
          degree_le_outerUpper
          (TraceAnalyticMotivicTStructure.Window.inclusion
            degree
            degree)
          (fun object => Eq.refl object.object)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        outerLower
        complex
        degree
        outerLower_le_degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
