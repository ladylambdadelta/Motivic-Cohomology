import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Counts.RewriteSteps.Owner

/-!
# Payload agreement under localized-arrow triple reassociation

This file records source and target payload agreement for the two
parenthesizations of the named localized-forward-arrow triple composite.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Reassociation preserves source imported rectangles for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles :=
  congrArg
    TraceLocalizationWordClass.sourceImportedRectangles
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves target imported rectangles for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles :=
  congrArg
    TraceLocalizationWordClass.targetImportedRectangles
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves source imported-rectangle count for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount :=
  congrArg
    TraceLocalizationWordClass.sourceImportedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves target imported-rectangle count for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount :=
  congrArg
    TraceLocalizationWordClass.targetImportedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves source certificate ledger for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger :=
  congrArg
    TraceLocalizationWordClass.sourceCertificateLedger
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves target certificate ledger for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger :=
  congrArg
    TraceLocalizationWordClass.targetCertificateLedger
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves source trace-bookkeeping count for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount :=
  congrArg
    TraceLocalizationWordClass.sourceTraceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves target trace-bookkeeping count for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount :=
  congrArg
    TraceLocalizationWordClass.targetTraceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves source rewrite-step count for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount :=
  congrArg
    TraceLocalizationWordClass.sourceRewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves target rewrite-step count for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount :=
  congrArg
    TraceLocalizationWordClass.targetRewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

end AnalyticMotives
end LFunctions
end Boundary
