import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Associativity.Owner

/-!
# Motive-root payload agreement under triple forward-word reassociation

This file exposes endpoint payload agreement for triple forward-word
reassociation through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the two unstable forward word parenthesizations agree. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord =
      triple.rightAssociatedUnstableForwardWord :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
    triple

/-- Motive-root wrapper: reassociation preserves source imported rectangles. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_sourceImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.rightAssociatedUnstableForwardWord.sourceImportedRectangles :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceImportedRectangles_eq
    triple

/-- Motive-root wrapper: reassociation preserves target imported rectangles. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_targetImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.rightAssociatedUnstableForwardWord.targetImportedRectangles :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetImportedRectangles_eq
    triple

/-- Motive-root wrapper: reassociation preserves source imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_sourceImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.sourceImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceImportedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves target imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_targetImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.targetImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetImportedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves source certificate ledger. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_sourceCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.rightAssociatedUnstableForwardWord.sourceCertificateLedger :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceCertificateLedger_eq
    triple

/-- Motive-root wrapper: reassociation preserves target certificate ledger. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_targetCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.rightAssociatedUnstableForwardWord.targetCertificateLedger :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetCertificateLedger_eq
    triple

/-- Motive-root wrapper: reassociation preserves source trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_sourceTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.sourceTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceTraceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves target trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_targetTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.targetTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetTraceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves source rewrite-step count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_sourceRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.sourceRewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceRewriteStepCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves target rewrite-step count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_targetRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.targetRewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetRewriteStepCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint imported rectangles. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_endpointImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointImportedRectangles_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_endpointImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointImportedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint certificate ledger. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_endpointCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_endpointTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.endpointTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointTraceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_endpointRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.endpointRewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointRewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
