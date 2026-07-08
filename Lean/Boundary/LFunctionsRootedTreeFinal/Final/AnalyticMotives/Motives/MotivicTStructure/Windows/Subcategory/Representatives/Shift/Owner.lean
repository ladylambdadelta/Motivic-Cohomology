import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Representatives.Transport.Owner

/-!
# Shifted representative constructors for window subcategories

This file turns the representative-level window shift laws into actual shifted
representative objects of the corresponding full subcategories.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A translated shifted bounded representative as an object of the translated
window. -/
def TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
    {lower upper : ℤ}
    (degree shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotivicTStructure.Window
      (lower + shift)
      (upper + shift) :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      (degree + shift),
    TraceAnalyticMotivicTStructure.window_of_shiftedBounded_add_right
      degree
      shift
      lower_le_degree
      degree_le_upper
      complex
  ⟩

/-- A translated shifted bounded representative as an object of its translated
singleton window. -/
def TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.Window
      (degree + shift)
      (degree + shift) :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      (degree + shift),
    TraceAnalyticMotivicTStructure.window_of_shiftedBounded_self_add_right
      shift
      complex
      degree
  ⟩

/-- The translated window representative has the expected ambient object. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight_object
    {lower upper : ℤ}
    (degree shift : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedAddRight
        degree
        shift
        lower_le_degree
        degree_le_upper
        complex).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

/-- The translated singleton-window representative has the expected ambient
object. -/
theorem TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight_object
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Window.ofShiftedBoundedSelfAddRight
        shift
        complex
        degree).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
