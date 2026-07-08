import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Owner

/-!
# Representatives for iso-closed analytic motivic aisles and coaisles

This file lifts the concrete shifted-bounded representative constructors into
the iso-closed predicates that are ready for Mathlib's `TStructure` fields.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A concrete shifted bounded representative in degree at most `cut` belongs
to the iso-closed analytic aisle at `cut`. -/
theorem TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed
      cut
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  TraceAnalyticMotivicTStructure.aisleLE_le_aisleLEIsoClosed
    cut
    (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      degree)
    (TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded
      cut
      complex
      degree
      degree_le)

/-- A concrete shifted bounded representative in degree at least `cut` belongs
to the iso-closed analytic coaisle at `cut`. -/
theorem TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
      cut
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  TraceAnalyticMotivicTStructure.coaisleGE_le_coaisleGEIsoClosed
    cut
    (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      degree)
    (TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded
      cut
      complex
      degree
      cut_le)

/-- A concrete shifted bounded representative lies in the iso-closed analytic
aisle at its own degree. -/
theorem TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded_self
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed
      degree
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded
    degree
    complex
    degree
    le_rfl

/-- A concrete shifted bounded representative lies in the iso-closed analytic
coaisle at its own degree. -/
theorem TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded_self
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
      degree
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded
    degree
    complex
    degree
    le_rfl

end AnalyticMotives
end LFunctions
end Boundary
