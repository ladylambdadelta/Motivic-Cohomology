import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Representatives.Shift.CutTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Shift.CutTransport.Projections.Owner

/-!
# Projection formulas after shifted heart-to-window cut transport

This file records the aisle and coaisle projections of translated
exact-degree heart representatives after mapping them into translated interval
windows and then applying translated wider-window cut transport.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- After translated wider-window cut transport, projecting the translated
interval-window image of a translated exact-degree heart representative to the
outer upper aisle gives the translated shifted bounded aisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindowAddRight_liftToWiderOfPointwiseEq_toAisle
    {outerLower innerLower degree innerUpper outerUpper : ℤ}
    (shift : ℤ)
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toAisle
        (outerLower + shift)
        (outerUpper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
          (add_le_add_right outerLower_le_innerLower shift)
          (add_le_add_right innerUpper_le_outerUpper shift)
          (TraceAnalyticMotivicTStructure.Window.inclusion
            (innerLower + shift)
            (innerUpper + shift))
          (fun object => Eq.refl object.object)).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            (add_le_add_right innerLower_le_degree shift)
            (add_le_add_right degree_le_innerUpper shift)).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        outerUpper
        shift
        complex
        degree
        (le_trans degree_le_innerUpper innerUpper_le_outerUpper) :=
  rfl

/-- After translated wider-window cut transport, projecting the translated
interval-window image of a translated exact-degree heart representative to the
outer lower coaisle gives the translated shifted bounded coaisle representative. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_toWindowAddRight_liftToWiderOfPointwiseEq_toCoaisle
    {outerLower innerLower degree innerUpper outerUpper : ℤ}
    (shift : ℤ)
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_degree : innerLower ≤ degree)
    (degree_le_innerUpper : degree ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.toCoaisle
        (outerLower + shift)
        (outerUpper + shift)).obj
        ((TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
          (add_le_add_right outerLower_le_innerLower shift)
          (add_le_add_right innerUpper_le_outerUpper shift)
          (TraceAnalyticMotivicTStructure.Window.inclusion
            (innerLower + shift)
            (innerUpper + shift))
          (fun object => Eq.refl object.object)).obj
          ((TraceAnalyticMotivicTStructure.Heart.toWindow
            (add_le_add_right innerLower_le_degree shift)
            (add_le_add_right degree_le_innerUpper shift)).obj
            (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree))) =
      TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        outerLower
        shift
        complex
        degree
        (le_trans outerLower_le_innerLower innerLower_le_degree) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
