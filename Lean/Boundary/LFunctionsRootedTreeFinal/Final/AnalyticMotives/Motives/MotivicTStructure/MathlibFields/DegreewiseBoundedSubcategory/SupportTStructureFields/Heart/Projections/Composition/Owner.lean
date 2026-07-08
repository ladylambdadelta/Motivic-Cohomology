import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Heart.Projections.Owner

/-!
# Composition identities for support-heart projections

This file records that the support-heart projections recover the support-heart
inclusion after composing with the corresponding support aisle and coaisle
inclusions.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Support-heart-to-aisle followed by support-aisle inclusion is the
support-heart inclusion. -/
theorem SupportHeart.toAisle_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportHeart.toAisle cut ⋙
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .SupportAisle.inclusion cut =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportHeart.inclusion cut :=
  rfl

/-- Support-heart-to-coaisle followed by support-coaisle inclusion is the
support-heart inclusion. -/
theorem SupportHeart.toCoaisle_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportHeart.toCoaisle cut ⋙
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .SupportCoaisle.inclusion cut =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportHeart.inclusion cut :=
  rfl

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
