import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.Owner

/-!
# Public payload agreement under localized-arrow triple reassociation

This file exposes source and target payload agreement for reassociation of
named localized-forward-arrow triple composites through the public
analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: reassociation preserves source imported rectangles. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_sourceImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceImportedRectangles_eq
    triple

/-- Public wrapper: reassociation preserves target imported rectangles. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_targetImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_targetImportedRectangles_eq
    triple

/-- Public wrapper: reassociation preserves source imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_sourceImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceImportedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves target imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_targetImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_targetImportedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves source certificate ledger. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_sourceCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceCertificateLedger_eq
    triple

/-- Public wrapper: reassociation preserves target certificate ledger. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_targetCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_targetCertificateLedger_eq
    triple

/-- Public wrapper: reassociation preserves source trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_sourceTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceTraceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves target trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_targetTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_targetTraceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves source rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_sourceRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceRewriteStepCount_eq
    triple

/-- Public wrapper: reassociation preserves target rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_targetRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_targetRewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
