import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Owner

/-!
# Support heart for the degreewise bounded stable source

This file defines the heart attached to the support-based aisle and coaisle
predicates on the degreewise bounded stable source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The support heart at `cut` is the intersection of the support `LE` and
support `GE` predicates at the same cut. -/
def supportHeart
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    Prop :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE cut object ∧
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE cut object

/-- Build support-heart membership from support aisle and coaisle membership. -/
theorem supportHeart_intro
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (aisle :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE cut object)
    (coaisle :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE cut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart cut object :=
  And.intro aisle coaisle

/-- Project support aisle membership from support-heart membership. -/
theorem supportHeart_aisle
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportHeart cut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE cut object :=
  membership.left

/-- Project support coaisle membership from support-heart membership. -/
theorem supportHeart_coaisle
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportHeart cut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE cut object :=
  membership.right

/-- The full subcategory of degreewise bounded stable objects in the support
heart at `cut`. -/
abbrev SupportHeart
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart cut)

/-- The degreewise bounded stable object carried by a support-heart object. -/
def SupportHeart.object
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  object.obj

/-- The support-heart membership certificate carried by a support-heart
object. -/
def SupportHeart.membership
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart cut object.object :=
  object.property

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
