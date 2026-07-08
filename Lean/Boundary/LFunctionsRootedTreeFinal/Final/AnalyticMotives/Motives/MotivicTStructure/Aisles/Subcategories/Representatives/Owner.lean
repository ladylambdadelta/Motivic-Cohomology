import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Transport.Owner

/-!
# Shifted bounded representatives as aisle and coaisle objects

This file turns shifted bounded analytic representative membership theorems
into actual objects of the aisle and coaisle full subcategories.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A shifted bounded representative in degree at most `cut` as an object of
the aisle at `cut`. -/
def TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    TraceAnalyticMotivicTStructure.Aisle cut :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      degree,
    TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded
      cut
      complex
      degree
      degree_le
  ⟩

/-- A shifted bounded representative in degree at least `cut` as an object of
the coaisle at `cut`. -/
def TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    TraceAnalyticMotivicTStructure.Coaisle cut :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      degree,
    TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded
      cut
      complex
      degree
      cut_le
  ⟩

/-- The aisle representative object has the expected ambient object. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded_object
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    (TraceAnalyticMotivicTStructure.Aisle.ofShiftedBounded
        cut
        complex
        degree
        degree_le).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

/-- The coaisle representative object has the expected ambient object. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded_object
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBounded
        cut
        complex
        degree
        cut_le).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
