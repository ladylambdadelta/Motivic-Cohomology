import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Representatives.Transport.Owner

/-!
# Shifted representative constructors for aisle and coaisle subcategories

This file turns the representative-level aisle and coaisle shift laws into
actual shifted representative objects of the corresponding full subcategories.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A translated shifted bounded representative as an object of the translated
aisle. -/
def TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    TraceAnalyticMotivicTStructure.Aisle (cut + shift) :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      (degree + shift),
    TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded_add_right
      cut
      shift
      complex
      degree
      degree_le
  ⟩

/-- A translated shifted bounded representative as an object of the translated
coaisle. -/
def TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    TraceAnalyticMotivicTStructure.Coaisle (cut + shift) :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      (degree + shift),
    TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded_add_right
      cut
      shift
      complex
      degree
      cut_le
  ⟩

/-- The translated aisle representative has the expected ambient object. -/
theorem TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight_object
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    (TraceAnalyticMotivicTStructure.Aisle.ofShiftedBoundedAddRight
        cut
        shift
        complex
        degree
        degree_le).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

/-- The translated coaisle representative has the expected ambient object. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight_object
    (cut shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    (TraceAnalyticMotivicTStructure.Coaisle.ofShiftedBoundedAddRight
        cut
        shift
        complex
        degree
        cut_le).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
