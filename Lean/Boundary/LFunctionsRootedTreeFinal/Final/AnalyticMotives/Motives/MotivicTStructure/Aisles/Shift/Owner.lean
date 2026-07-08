import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.CutTransport.Owner

/-!
# Shifted representatives in analytic motivic aisles and coaisles

This file proves the cut-shift laws that are already available from the
concrete shifted bounded analytic representatives.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Translating the representative degree and the aisle cut by the same integer
preserves the concrete shifted-bounded aisle membership theorem. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded_add_right
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    TraceAnalyticMotivicTStructure.aisleLE
      (cut + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded
    (cut + shift)
    complex
    (degree + shift)
    (add_le_add_right degree_le shift)

/-- Translating the representative degree and the coaisle cut by the same
integer preserves the concrete shifted-bounded coaisle membership theorem. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded_add_right
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    TraceAnalyticMotivicTStructure.coaisleGE
      (cut + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded
    (cut + shift)
    complex
    (degree + shift)
    (add_le_add_right cut_le shift)

/-- A shifted bounded analytic representative lies in the translated aisle at
the translated degree cut. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded_self_add_right
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.aisleLE
      (degree + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded_add_right
    degree
    shift
    complex
    degree
    le_rfl

/-- A shifted bounded analytic representative lies in the translated coaisle at
the translated degree cut. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded_self_add_right
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.coaisleGE
      (degree + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded_add_right
    degree
    shift
    complex
    degree
    le_rfl

end AnalyticMotives
end LFunctions
end Boundary
