import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Transport.Owner

/-!
# Concrete windows for the analytic motivic t-structure

This file defines interval windows as the intersection of a lower coaisle and
an upper aisle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic motivic window from `lower` to `upper`: objects in the
coaisle at `lower` and in the aisle at `upper`. -/
def TraceAnalyticMotivicTStructure.window
    (lower upper : ℤ)
    (object : TraceAnalyticDMgmComparisonSource) :
    Prop :=
  TraceAnalyticMotivicTStructure.coaisleGE lower object ∧
    TraceAnalyticMotivicTStructure.aisleLE upper object

/-- Build window membership from coaisle and aisle membership. -/
theorem TraceAnalyticMotivicTStructure.window_intro
    {lower upper : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (coaisle :
      TraceAnalyticMotivicTStructure.coaisleGE lower object)
    (aisle :
      TraceAnalyticMotivicTStructure.aisleLE upper object) :
    TraceAnalyticMotivicTStructure.window lower upper object :=
  And.intro coaisle aisle

/-- Project lower-coaisle membership from window membership. -/
theorem TraceAnalyticMotivicTStructure.window_coaisle
    {lower upper : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.window lower upper object) :
    TraceAnalyticMotivicTStructure.coaisleGE lower object :=
  membership.left

/-- Project upper-aisle membership from window membership. -/
theorem TraceAnalyticMotivicTStructure.window_aisle
    {lower upper : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.window lower upper object) :
    TraceAnalyticMotivicTStructure.aisleLE upper object :=
  membership.right

/-- A shifted bounded representative with degree inside the interval belongs
to the corresponding window. -/
theorem TraceAnalyticMotivicTStructure.window_of_shiftedBounded
    {lower upper : ℤ}
    (degree : ℤ)
    (lower_le_degree : lower ≤ degree)
    (degree_le_upper : degree ≤ upper)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotivicTStructure.window
      lower
      upper
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  TraceAnalyticMotivicTStructure.window_intro
    (TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded
      lower
      complex
      degree
      lower_le_degree)
    (TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded
      upper
      complex
      degree
      degree_le_upper)

/-- A heart object at `center` lies in every enclosing window. -/
theorem TraceAnalyticMotivicTStructure.window_of_heartAt
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.heartAt center object) :
    TraceAnalyticMotivicTStructure.window lower upper object :=
  TraceAnalyticMotivicTStructure.window_intro
    (TraceAnalyticMotivicTStructure.coaisleGE_mono
      lower_le_center
      (TraceAnalyticMotivicTStructure.heartAt_coaisle membership))
    (TraceAnalyticMotivicTStructure.aisleLE_mono
      center_le_upper
      (TraceAnalyticMotivicTStructure.heartAt_aisle membership))

end AnalyticMotives
end LFunctions
end Boundary
