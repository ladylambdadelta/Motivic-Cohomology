import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Heart.Projections.Owner

/-!
# Shifted bounded representatives as iso-closed heart objects

This file turns exact-degree shifted bounded analytic representatives into
objects of the iso-closed analytic motivic heart.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A shifted bounded representative as an object of the iso-closed heart at
its own degree. -/
def TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed degree :=
  ⟨
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
      complex
      degree,
    TraceAnalyticMotivicTStructure.heartAtIsoClosed_of_shiftedBounded_self
      complex
      degree
  ⟩

/-- The exact-degree iso-closed heart representative has the expected ambient
object. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf_object
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf
        complex
        degree).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

/-- The exact-degree iso-closed heart representative projects to the expected
iso-closed aisle object. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf_toAisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisle degree).obj
        (TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisleObject
        (TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf
          complex
          degree) :=
  rfl

/-- The exact-degree iso-closed heart representative projects to the expected
iso-closed coaisle object. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf_toCoaisle
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisle degree).obj
        (TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf
          complex
          degree) =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisleObject
        (TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf
          complex
          degree) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
