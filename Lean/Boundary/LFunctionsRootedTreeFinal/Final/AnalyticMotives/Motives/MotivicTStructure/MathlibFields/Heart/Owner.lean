import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Fields.Owner

/-!
# Iso-closed analytic motivic heart

This file defines the heart attached to the Mathlib-ready iso-closed analytic
aisle and coaisle predicates.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The iso-closed cutwise analytic motivic heart is the intersection of the
iso-closed analytic aisle and coaisle predicates at the same cut. -/
def TraceAnalyticMotivicTStructure.heartAtIsoClosed
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource) :
    Prop :=
  TraceAnalyticMotivicTStructure.aisleLEIsoClosed cut object ∧
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed cut object

/-- Build iso-closed heart membership from iso-closed aisle and coaisle
membership. -/
theorem TraceAnalyticMotivicTStructure.heartAtIsoClosed_intro
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (aisle :
      TraceAnalyticMotivicTStructure.aisleLEIsoClosed cut object)
    (coaisle :
      TraceAnalyticMotivicTStructure.coaisleGEIsoClosed cut object) :
    TraceAnalyticMotivicTStructure.heartAtIsoClosed cut object :=
  And.intro aisle coaisle

/-- Project iso-closed aisle membership from iso-closed heart membership. -/
theorem TraceAnalyticMotivicTStructure.heartAtIsoClosed_aisle
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.heartAtIsoClosed cut object) :
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed cut object :=
  membership.left

/-- Project iso-closed coaisle membership from iso-closed heart membership. -/
theorem TraceAnalyticMotivicTStructure.heartAtIsoClosed_coaisle
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.heartAtIsoClosed cut object) :
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed cut object :=
  membership.right

/-- A concrete shifted bounded representative lies in the iso-closed heart at
its own shift degree. -/
theorem TraceAnalyticMotivicTStructure.heartAtIsoClosed_of_shiftedBounded_self
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.heartAtIsoClosed
      degree
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  TraceAnalyticMotivicTStructure.heartAtIsoClosed_intro
    (TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded_self
      complex
      degree)
    (TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded_self
      complex
      degree)

/-- The full subcategory of objects in the iso-closed analytic motivic heart at
`cut`. -/
abbrev TraceAnalyticMotivicTStructure.HeartIsoClosed
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticMotivicTStructure.heartAtIsoClosed cut)

/-- The ambient stable comparison-source object carried by an iso-closed heart
object. -/
def TraceAnalyticMotivicTStructure.HeartIsoClosed.object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    TraceAnalyticDMgmComparisonSource :=
  object.obj

/-- The iso-closed heart membership certificate carried by an iso-closed heart
object. -/
def TraceAnalyticMotivicTStructure.HeartIsoClosed.membership
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    TraceAnalyticMotivicTStructure.heartAtIsoClosed cut object.object :=
  object.property

/-- A concrete analytic heart object at cut `cut` is a Mathlib-facing
`TStructure` heart object at the reindexed cut `-cut`. -/
theorem TraceAnalyticMotivicTStructure.heartAtIsoClosed_to_tStructureHeart
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.heartAtIsoClosed cut object) :
    TraceAnalyticMotivicTStructure.tStructureLE (-cut) object ∧
      TraceAnalyticMotivicTStructure.tStructureGE (-cut) object :=
  And.intro
    (Eq.subst
      (motive := fun reindexedCut =>
        TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
          reindexedCut
          object)
      (neg_neg cut).symm
      membership.right)
    (Eq.subst
      (motive := fun reindexedCut =>
        TraceAnalyticMotivicTStructure.aisleLEIsoClosed
          reindexedCut
          object)
      (neg_neg cut).symm
      membership.left)

/-- A Mathlib-facing `TStructure` heart object at cut `-cut` is a concrete
analytic heart object at cut `cut`. -/
theorem TraceAnalyticMotivicTStructure.heartAtIsoClosed_of_tStructureHeart
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.tStructureLE (-cut) object ∧
        TraceAnalyticMotivicTStructure.tStructureGE (-cut) object) :
    TraceAnalyticMotivicTStructure.heartAtIsoClosed cut object :=
  TraceAnalyticMotivicTStructure.heartAtIsoClosed_intro
    (Eq.subst
      (motive := fun reindexedCut =>
        TraceAnalyticMotivicTStructure.aisleLEIsoClosed
          reindexedCut
          object)
      (neg_neg cut)
      membership.right)
    (Eq.subst
      (motive := fun reindexedCut =>
        TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
          reindexedCut
          object)
      (neg_neg cut)
      membership.left)

end AnalyticMotives
end LFunctions
end Boundary
