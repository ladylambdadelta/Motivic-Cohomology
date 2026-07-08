import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Associativity.Owner

/-!
# Public payload agreement under triple forward-word reassociation

This file exposes endpoint payload agreement for triple forward-word
reassociation through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the two unstable forward word parenthesizations agree. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord =
      triple.rightAssociatedUnstableForwardWord :=
  TraceAnalyticMotive.associatedUnstableForwardWord_eq
    triple

/-- Public wrapper: reassociation preserves source imported rectangles. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_sourceImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.rightAssociatedUnstableForwardWord.sourceImportedRectangles :=
  TraceAnalyticMotive.associatedUnstableForwardWord_sourceImportedRectangles_eq
    triple

/-- Public wrapper: reassociation preserves target imported rectangles. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_targetImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.rightAssociatedUnstableForwardWord.targetImportedRectangles :=
  TraceAnalyticMotive.associatedUnstableForwardWord_targetImportedRectangles_eq
    triple

/-- Public wrapper: reassociation preserves source imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_sourceImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.sourceImportedRectangleCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_sourceImportedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves target imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_targetImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.targetImportedRectangleCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_targetImportedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves source certificate ledger. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_sourceCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.rightAssociatedUnstableForwardWord.sourceCertificateLedger :=
  TraceAnalyticMotive.associatedUnstableForwardWord_sourceCertificateLedger_eq
    triple

/-- Public wrapper: reassociation preserves target certificate ledger. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_targetCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.rightAssociatedUnstableForwardWord.targetCertificateLedger :=
  TraceAnalyticMotive.associatedUnstableForwardWord_targetCertificateLedger_eq
    triple

/-- Public wrapper: reassociation preserves source trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_sourceTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.sourceTraceBookkeepingCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_sourceTraceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves target trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_targetTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.targetTraceBookkeepingCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_targetTraceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves source rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_sourceRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.sourceRewriteStepCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_sourceRewriteStepCount_eq
    triple

/-- Public wrapper: reassociation preserves target rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_targetRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.targetRewriteStepCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_targetRewriteStepCount_eq
    triple

/-- Public wrapper: reassociation preserves endpoint imported rectangles. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_endpointImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles :=
  TraceAnalyticMotive.associatedUnstableForwardWord_endpointImportedRectangles_eq
    triple

/-- Public wrapper: reassociation preserves endpoint imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_endpointImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_endpointImportedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves endpoint certificate ledger. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_endpointCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger :=
  TraceAnalyticMotive.associatedUnstableForwardWord_endpointCertificateLedger_eq
    triple

/-- Public wrapper: reassociation preserves endpoint trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_endpointTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.endpointTraceBookkeepingCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_endpointTraceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_endpointRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.endpointRewriteStepCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_endpointRewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
