import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Counts.Owner

/-!
# Motive-root endpoint counts of localized-arrow triple composites

This file exposes source and target count projections for the two named
localized-forward-arrow triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated localized-arrow source imported count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.localizedForwardArrow.sourceImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    triple

/-- Motive-root wrapper: left-associated localized-arrow target imported count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.localizedForwardArrow.targetImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    triple

/-- Motive-root wrapper: right-associated localized-arrow source imported count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.localizedForwardArrow.sourceImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    triple

/-- Motive-root wrapper: right-associated localized-arrow target imported count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.localizedForwardArrow.targetImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    triple

/-- Motive-root wrapper: left-associated localized-arrow source bookkeeping count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.localizedForwardArrow.sourceTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    triple

/-- Motive-root wrapper: left-associated localized-arrow target bookkeeping count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.localizedForwardArrow.targetTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    triple

/-- Motive-root wrapper: right-associated localized-arrow source bookkeeping count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.localizedForwardArrow.sourceTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    triple

/-- Motive-root wrapper: right-associated localized-arrow target bookkeeping count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.localizedForwardArrow.targetTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
