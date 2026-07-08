import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.Projections.Owner

/-!
# Projection formulas after monotone widening for translated window representatives

This file records the aisle and coaisle projections of translated shifted
bounded window representatives after inclusion into translated wider interval
windows.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After translated monotone widening, projecting a translated shifted bounded
window representative to the translated outer upper aisle gives the translated
shifted bounded aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight_inclusionOfBounds_toAisle
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (degree shift : ℤ)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        (outerLower + shift)
        (outerUpper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
          (add_le_add_right outerLower_le_innerLower shift)
          (add_le_add_right innerUpper_le_outerUpper shift)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
            degree
            shift
            innerLower_le_degree
            degree_le_innerUpper
            complex)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        outerUpper
        shift
        complex
        degree
        (le_trans degree_le_innerUpper innerUpper_le_outerUpper) :=
  rfl

/-- After translated monotone widening, projecting a translated shifted bounded
window representative to the translated outer lower coaisle gives the
translated shifted bounded coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight_inclusionOfBounds_toCoaisle
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (degree shift : ℤ)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        (outerLower + shift)
        (outerUpper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
          (add_le_add_right outerLower_le_innerLower shift)
          (add_le_add_right innerUpper_le_outerUpper shift)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
            degree
            shift
            innerLower_le_degree
            degree_le_innerUpper
            complex)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        outerLower
        shift
        complex
        degree
        (le_trans outerLower_le_innerLower innerLower_le_degree) :=
  rfl

/-- After translated monotone widening, projecting a translated singleton
window representative to the translated outer upper aisle gives the translated
shifted bounded aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_inclusionOfBounds_toAisle
    {outerLower degree outerUpper : ℤ}
    (outerLower_le_degree : outerLower ≤ degree)
    (degree_le_outerUpper : degree ≤ outerUpper)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        (outerLower + shift)
        (outerUpper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
          (add_le_add_right outerLower_le_degree shift)
          (add_le_add_right degree_le_outerUpper shift)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        outerUpper
        shift
        complex
        degree
        degree_le_outerUpper :=
  rfl

/-- After translated monotone widening, projecting a translated singleton
window representative to the translated outer lower coaisle gives the
translated shifted bounded coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_inclusionOfBounds_toCoaisle
    {outerLower degree outerUpper : ℤ}
    (outerLower_le_degree : outerLower ≤ degree)
    (degree_le_outerUpper : degree ≤ outerUpper)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        (outerLower + shift)
        (outerUpper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
          (add_le_add_right outerLower_le_degree shift)
          (add_le_add_right degree_le_outerUpper shift)).obj
          (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        outerLower
        shift
        complex
        degree
        outerLower_le_degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
