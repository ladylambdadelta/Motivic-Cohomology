import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Heart.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Shift.Owner

/-!
# Shift closure for the support heart

This file proves that support-heart membership is transported by shifts in the
same cut-reindexing convention used by the support `LE` and `GE` fields.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The support heart is stable under shifts with the same cut relation as the
support `LE` and `GE` predicates. -/
theorem supportHeart_shift
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportHeart sourceCut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart targetCut (object⟦shift⟧) :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportHeart_intro
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE_shift
          sourceCut
          shift
          targetCut
          cut_eq
          object
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportHeart_aisle membership))
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE_shift
          sourceCut
          shift
          targetCut
          cut_eq
          object
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportHeart_coaisle membership))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
