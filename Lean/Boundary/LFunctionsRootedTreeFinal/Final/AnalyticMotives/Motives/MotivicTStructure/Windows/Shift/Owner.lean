import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Transport.Owner

/-!
# Shifted representatives in analytic motivic windows

This file proves representative-level shift laws for concrete analytic motivic
window membership.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Translating the representative degree and both window bounds by the same
integer preserves shifted-bounded window membership. -/
theorem TraceAnalyticMotivicTStructure.window_of_shiftedBounded_add_right
    {lower upper : ℤ}
    (degree shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotivicTStructure.window
      (lower + shift)
      (upper + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.window_of_shiftedBounded
    (degree + shift)
    (add_le_add_right lower_le_degree shift)
    (add_le_add_right degree_le_upper shift)
    complex

/-- A shifted bounded representative lies in the singleton window at its own
shifted degree. -/
theorem TraceAnalyticMotivicTStructure.window_of_shiftedBounded_self
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.window
      degree
      degree
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  TraceAnalyticMotivicTStructure.window_of_shiftedBounded
    degree
    le_rfl
    le_rfl
    complex

/-- Exact singleton-window membership for shifted bounded representatives is
stable under translating the representative degree. -/
theorem TraceAnalyticMotivicTStructure.window_of_shiftedBounded_self_add_right
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.window
      (degree + shift)
      (degree + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.window_of_shiftedBounded_add_right
    degree
    shift
    le_rfl
    le_rfl
    complex

end AnalyticMotives
end LFunctions
end Boundary
