import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Representatives.Owner

/-!
# Shifted representatives for iso-closed analytic motivic predicates

This file lifts the concrete translated shifted-bounded representative
membership theorems into the Mathlib-ready iso-closed aisle and coaisle
predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Translating the representative degree and the aisle cut by the same integer
preserves iso-closed analytic aisle membership. -/
theorem TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded_add_right
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed
      (cut + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.aisleLE_le_aisleLEIsoClosed
    (cut + shift)
    (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      (degree + shift))
    (TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded_add_right
      cut
      shift
      complex
      degree
      degree_le)

/-- Translating the representative degree and the coaisle cut by the same
integer preserves iso-closed analytic coaisle membership. -/
theorem TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded_add_right
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
      (cut + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.coaisleGE_le_coaisleGEIsoClosed
    (cut + shift)
    (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      (degree + shift))
    (TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded_add_right
      cut
      shift
      complex
      degree
      cut_le)

/-- A translated shifted bounded representative lies in the translated
iso-closed analytic aisle at its translated degree. -/
theorem TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded_self_add_right
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed
      (degree + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded_add_right
    degree
    shift
    complex
    degree
    le_rfl

/-- A translated shifted bounded representative lies in the translated
iso-closed analytic coaisle at its translated degree. -/
theorem TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded_self_add_right
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
      (degree + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded_add_right
    degree
    shift
    complex
    degree
    le_rfl

end AnalyticMotives
end LFunctions
end Boundary
