import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Shift.Owner

/-!
# The concrete analytic motivic heart

This file defines the cutwise heart as the intersection of the concrete
analytic motivic aisle and coaisle predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The cutwise analytic motivic heart is the intersection of aisle and coaisle
membership at the same cut. -/
def TraceAnalyticMotivicTStructure.heartAt
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource) :
    Prop :=
  TraceAnalyticMotivicTStructure.aisleLE cut object ∧
    TraceAnalyticMotivicTStructure.coaisleGE cut object

/-- Build heart membership from aisle and coaisle membership. -/
theorem TraceAnalyticMotivicTStructure.heartAt_intro
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (aisle :
      TraceAnalyticMotivicTStructure.aisleLE cut object)
    (coaisle :
      TraceAnalyticMotivicTStructure.coaisleGE cut object) :
    TraceAnalyticMotivicTStructure.heartAt cut object :=
  And.intro aisle coaisle

/-- Project aisle membership from heart membership. -/
theorem TraceAnalyticMotivicTStructure.heartAt_aisle
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.heartAt cut object) :
    TraceAnalyticMotivicTStructure.aisleLE cut object :=
  membership.left

/-- Project coaisle membership from heart membership. -/
theorem TraceAnalyticMotivicTStructure.heartAt_coaisle
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.heartAt cut object) :
    TraceAnalyticMotivicTStructure.coaisleGE cut object :=
  membership.right

/-- A shifted bounded analytic representative lies in the heart at its own
shift degree. -/
theorem TraceAnalyticMotivicTStructure.heartAt_of_shiftedBounded_self
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.heartAt
      degree
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  TraceAnalyticMotivicTStructure.heartAt_intro
    (TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded
      complex
      degree
      degree
      le_rfl)
    (TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded
      complex
      degree
      degree
      le_rfl)

/-- A degree-zero shifted bounded analytic representative lies in the zero
heart. -/
theorem TraceAnalyticMotivicTStructure.heartAt_zero_of_shiftedBounded
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotivicTStructure.heartAt
      0
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        0) :=
  TraceAnalyticMotivicTStructure.heartAt_of_shiftedBounded_self
    complex
    0

/-- Exact-degree shifted heart membership is stable under translating the
representative degree. -/
theorem TraceAnalyticMotivicTStructure.heartAt_of_shiftedBounded_self_add_right
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.heartAt
      (degree + shift)
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift)) :=
  TraceAnalyticMotivicTStructure.heartAt_intro
    (TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded_self_add_right
      shift
      complex
      degree)
    (TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded_self_add_right
      shift
      complex
      degree)

end AnalyticMotives
end LFunctions
end Boundary
