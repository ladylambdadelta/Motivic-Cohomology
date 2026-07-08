import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Counts.Owner

/-!
# Public endpoint counts of localized-arrow triple composites

This file exposes source and target count projections for the two named
localized-forward-arrow triple composites through the public analytic-motives
root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated localized-arrow source imported count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.localizedForwardArrow.sourceImportedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    triple

/-- Public wrapper: left-associated localized-arrow target imported count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.localizedForwardArrow.targetImportedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    triple

/-- Public wrapper: right-associated localized-arrow source imported count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.localizedForwardArrow.sourceImportedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    triple

/-- Public wrapper: right-associated localized-arrow target imported count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.localizedForwardArrow.targetImportedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    triple

/-- Public wrapper: left-associated localized-arrow source bookkeeping count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.localizedForwardArrow.sourceTraceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    triple

/-- Public wrapper: left-associated localized-arrow target bookkeeping count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.localizedForwardArrow.targetTraceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    triple

/-- Public wrapper: right-associated localized-arrow source bookkeeping count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.localizedForwardArrow.sourceTraceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    triple

/-- Public wrapper: right-associated localized-arrow target bookkeeping count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.localizedForwardArrow.targetTraceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
