import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Owner

/-!
# Payload agreement under triple forward-word reassociation

This file records that the two parenthesizations of a composable triple of
unstable forward words have the same endpoint payload.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The two parenthesizations of the unstable forward word composite agree. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord =
      triple.rightAssociatedUnstableForwardWord :=
  TraceLocalizationInputComposableTriple.unstableForward_wordClass_assoc
    triple

/-- Reassociation preserves source imported rectangles. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.rightAssociatedUnstableForwardWord.sourceImportedRectangles :=
  congrArg
    TraceLocalizationWordClass.sourceImportedRectangles
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves target imported rectangles. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.rightAssociatedUnstableForwardWord.targetImportedRectangles :=
  congrArg
    TraceLocalizationWordClass.targetImportedRectangles
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves source imported-rectangle count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.sourceImportedRectangleCount :=
  congrArg
    TraceLocalizationWordClass.sourceImportedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves target imported-rectangle count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.targetImportedRectangleCount :=
  congrArg
    TraceLocalizationWordClass.targetImportedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves source certificate ledger. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.rightAssociatedUnstableForwardWord.sourceCertificateLedger :=
  congrArg
    TraceLocalizationWordClass.sourceCertificateLedger
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves target certificate ledger. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.rightAssociatedUnstableForwardWord.targetCertificateLedger :=
  congrArg
    TraceLocalizationWordClass.targetCertificateLedger
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves source trace-bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.sourceTraceBookkeepingCount :=
  congrArg
    TraceLocalizationWordClass.sourceTraceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves target trace-bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.targetTraceBookkeepingCount :=
  congrArg
    TraceLocalizationWordClass.targetTraceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves source rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_sourceRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.sourceRewriteStepCount :=
  congrArg
    TraceLocalizationWordClass.sourceRewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves target rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_targetRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.targetRewriteStepCount :=
  congrArg
    TraceLocalizationWordClass.targetRewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves endpoint imported rectangles. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles :=
  congrArg
    TraceLocalizationWordClass.endpointImportedRectangles
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves endpoint imported-rectangle count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount :=
  congrArg
    TraceLocalizationWordClass.endpointImportedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves endpoint certificate ledger. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger :=
  congrArg
    TraceLocalizationWordClass.endpointCertificateLedger
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves endpoint trace-bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.endpointTraceBookkeepingCount :=
  congrArg
    TraceLocalizationWordClass.endpointTraceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

/-- Reassociation preserves endpoint rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.endpointRewriteStepCount :=
  congrArg
    TraceLocalizationWordClass.endpointRewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_eq
      triple)

end AnalyticMotives
end LFunctions
end Boundary
