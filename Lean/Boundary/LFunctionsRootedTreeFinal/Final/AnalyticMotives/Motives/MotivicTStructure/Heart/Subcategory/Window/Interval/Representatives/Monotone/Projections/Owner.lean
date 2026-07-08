import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Projections.Owner

/-!
# Projection formulas after monotone widening for heart-to-window representatives

This file records the aisle and coaisle projections of exact-degree heart
representative images after widening the target interval window.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After monotone widening, projecting an exact-degree heart-to-window
representative image to the outer upper aisle gives the corresponding aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_inclusionOfBounds_toAisle
    {outerLower innerLower center innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_center : innerLower ≤ center)
    (center_le_innerUpper : center ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        outerLower
        outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
          outerLower_le_innerLower
          innerUpper_le_outerUpper).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            innerLower_le_center
            center_le_innerUpper).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
              complex
              center))) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        outerUpper
        complex
        center
        (le_trans center_le_innerUpper innerUpper_le_outerUpper) :=
  rfl

/-- After monotone widening, projecting an exact-degree heart-to-window
representative image to the outer lower coaisle gives the corresponding
coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_toWindow_inclusionOfBounds_toCoaisle
    {outerLower innerLower center innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_center : innerLower ≤ center)
    (center_le_innerUpper : center ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        outerLower
        outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
          outerLower_le_innerLower
          innerUpper_le_outerUpper).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            innerLower_le_center
            center_le_innerUpper).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
              complex
              center))) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        outerLower
        complex
        center
        (le_trans outerLower_le_innerLower innerLower_le_center) :=
  rfl

/-- After monotone widening, projecting a translated heart-to-window
representative image to the outer upper aisle gives the corresponding aisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_inclusionOfBounds_toAisle
    {outerLower innerLower degree innerUpper outerUpper shift : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_degree_shift : innerLower ≤ degree + shift)
    (degree_shift_le_innerUpper : degree + shift ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        outerLower
        outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
          outerLower_le_innerLower
          innerUpper_le_outerUpper).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            innerLower_le_degree_shift
            degree_shift_le_innerUpper).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        outerUpper
        complex
        (degree + shift)
        (le_trans degree_shift_le_innerUpper innerUpper_le_outerUpper) :=
  rfl

/-- After monotone widening, projecting a translated heart-to-window
representative image to the outer lower coaisle gives the corresponding coaisle
representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindow_inclusionOfBounds_toCoaisle
    {outerLower innerLower degree innerUpper outerUpper shift : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_degree_shift : innerLower ≤ degree + shift)
    (degree_shift_le_innerUpper : degree + shift ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        outerLower
        outerUpper).obj
        ((TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
          outerLower_le_innerLower
          innerUpper_le_outerUpper).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            innerLower_le_degree_shift
            degree_shift_le_innerUpper).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        outerLower
        complex
        (degree + shift)
        (le_trans outerLower_le_innerLower innerLower_le_degree_shift) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
