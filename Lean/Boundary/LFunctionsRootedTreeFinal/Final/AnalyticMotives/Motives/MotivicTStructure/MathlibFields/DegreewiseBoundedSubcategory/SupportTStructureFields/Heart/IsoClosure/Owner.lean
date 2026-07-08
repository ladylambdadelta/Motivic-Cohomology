import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Heart.Owner

/-!
# Isomorphism closure for the support heart

This file proves that the support heart is closed under isomorphism in the
degreewise bounded stable source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The support heart is closed under isomorphisms in the degreewise bounded
stable source. -/
def supportHeart_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportHeart cut) where
  of_iso :=
    fun iso sourceMembership =>
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportHeart_intro
        ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureLE_closedUnderIsomorphisms cut).of_iso
            iso
            (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .supportHeart_aisle sourceMembership))
        ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureGE_closedUnderIsomorphisms cut).of_iso
            iso
            (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .supportHeart_coaisle sourceMembership))

/-- Transport support-heart membership across an isomorphism. -/
theorem supportHeart_of_iso
    {cut : ℤ}
    {source target : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (iso : source ≅ target)
    (sourceMembership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportHeart cut source) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart cut target :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportHeart_closedUnderIsomorphisms cut).of_iso
      iso
      sourceMembership

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
