import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.Owner

/-!
# Motive-root payload agreement under localized-arrow triple reassociation

This file exposes source and target payload agreement for reassociation of
named localized-forward-arrow triple composites through the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: reassociation preserves source imported rectangles. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceImportedRectangles_eq
    triple

/-- Motive-root wrapper: reassociation preserves target imported rectangles. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_targetImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetImportedRectangles_eq
    triple

/-- Motive-root wrapper: reassociation preserves source imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceImportedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves target imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_targetImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetImportedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves source certificate ledger. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_eq
    triple

/-- Motive-root wrapper: reassociation preserves target certificate ledger. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_targetCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_eq
    triple

/-- Motive-root wrapper: reassociation preserves source trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceTraceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves target trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_targetTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetTraceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves source rewrite-step count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceRewriteStepCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves target rewrite-step count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_targetRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetRewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
