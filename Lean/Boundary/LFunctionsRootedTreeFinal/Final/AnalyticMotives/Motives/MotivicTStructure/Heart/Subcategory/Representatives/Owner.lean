import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Owner

/-!
# Shifted bounded representatives as heart objects

This file turns exact-degree shifted bounded analytic representatives into
objects of the concrete analytic motivic heart.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A shifted bounded representative as an object of the heart at its own
degree. -/
def TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.Heart degree :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      degree,
    TraceAnalyticMotivicTStructure.heartAt_of_shiftedBounded_self
      complex
      degree
  ⟩

/-- A translated shifted bounded representative as an object of the translated
heart. -/
def TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.Heart (degree + shift) :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      (degree + shift),
    TraceAnalyticMotivicTStructure.heartAt_of_shiftedBounded_self_add_right
      shift
      complex
      degree
  ⟩

/-- The exact-degree heart representative has the expected ambient object. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf_object
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
        complex
        degree).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

/-- The translated exact-degree heart representative has the expected ambient
object. -/
theorem TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight_object
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
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
