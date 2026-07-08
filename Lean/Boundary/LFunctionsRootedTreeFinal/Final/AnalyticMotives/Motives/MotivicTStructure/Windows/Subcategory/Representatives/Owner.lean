import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Owner

/-!
# Shifted bounded representatives as window objects

This file turns shifted bounded analytic representative membership into actual
objects of analytic motivic window subcategories.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A shifted bounded representative inside an interval as an object of the
corresponding window. -/
def TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
    {lower upper : ℤ}
    (degree : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotivicTStructure.Window lower upper :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      degree,
    TraceAnalyticMotivicTStructure.window_of_shiftedBounded
      degree
      lower_le_degree
      degree_le_upper
      complex
  ⟩

/-- A shifted bounded representative as an object of its singleton window. -/
def TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.Window degree degree :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      degree,
    TraceAnalyticMotivicTStructure.window_of_shiftedBounded_self
      complex
      degree
  ⟩

/-- A shifted bounded representative inside an interval has the expected
ambient object. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBounded_object
    {lower upper : ℤ}
    (degree : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.ofShiftedBounded
        degree
        lower_le_degree
        degree_le_upper
        complex).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

/-- A shifted bounded representative in its singleton window has the expected
ambient object. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf_object
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelf
        complex
        degree).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
