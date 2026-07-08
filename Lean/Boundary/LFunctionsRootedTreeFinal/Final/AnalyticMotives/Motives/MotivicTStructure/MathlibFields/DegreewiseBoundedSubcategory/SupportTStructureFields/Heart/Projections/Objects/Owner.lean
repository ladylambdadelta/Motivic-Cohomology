import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Heart.Projections.Owner

/-!
# Object identities for support-heart projections

This file records the object-level inclusion identities for support-heart
projections to the support aisle and support coaisle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Projecting a support-heart object to the support aisle and then including
it recovers the heart object's carried degreewise bounded stable object. -/
theorem SupportHeart.toAisle_inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportAisle.inclusion cut).obj
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .SupportHeart.toAisleObject object) =
      object.object :=
  rfl

/-- Projecting a support-heart object to the support coaisle and then including
it recovers the heart object's carried degreewise bounded stable object. -/
theorem SupportHeart.toCoaisle_inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportCoaisle.inclusion cut).obj
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .SupportHeart.toCoaisleObject object) =
      object.object :=
  rfl

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
