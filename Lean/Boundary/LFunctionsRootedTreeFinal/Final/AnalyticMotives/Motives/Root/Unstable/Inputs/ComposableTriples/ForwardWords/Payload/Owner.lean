import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Associativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Endpoint.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.ObjectCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.ObjectPayload.Owner

/-!
# Motive-root payload of triple forward words

This file exposes endpoint payload facts for the two parenthesizations of
unstable forward-word composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated unstable forward word composite. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord =
      TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord triple :=
  rfl

/-- Motive-root wrapper: right-associated unstable forward word composite. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord =
      TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord triple :=
  rfl

/-- Motive-root wrapper: the left-associated triple forward word keeps first source rectangles. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.unstableForward.sourceImportedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceImportedRectangles
    triple

/-- Motive-root wrapper: the left-associated triple forward word keeps third target rectangles. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.unstableForward.targetImportedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetImportedRectangles
    triple

/-- Motive-root wrapper: the right-associated triple forward word keeps first source rectangles. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.unstableForward.sourceImportedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceImportedRectangles
    triple

/-- Motive-root wrapper: the right-associated triple forward word keeps third target rectangles. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.unstableForward.targetImportedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetImportedRectangles
    triple

/-- Motive-root wrapper: the left-associated triple forward word keeps first source ledger. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.unstableForward.sourceCertificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceCertificateLedger
    triple

/-- Motive-root wrapper: the left-associated triple forward word keeps third target ledger. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.unstableForward.targetCertificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetCertificateLedger
    triple

/-- Motive-root wrapper: the right-associated triple forward word keeps first source ledger. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.unstableForward.sourceCertificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceCertificateLedger
    triple

/-- Motive-root wrapper: the right-associated triple forward word keeps third target ledger. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.unstableForward.targetCertificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetCertificateLedger
    triple

/-- Motive-root wrapper: the left-associated triple forward word keeps first source bookkeeping count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.unstableForward.sourceTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    triple

/-- Motive-root wrapper: the left-associated triple forward word keeps third target bookkeeping count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.unstableForward.targetTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    triple

/-- Motive-root wrapper: the right-associated triple forward word keeps first source bookkeeping count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.unstableForward.sourceTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    triple

/-- Motive-root wrapper: the right-associated triple forward word keeps third target bookkeeping count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.unstableForward.targetTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    triple

/-- Motive-root wrapper: the left-associated triple forward word keeps first source rewrite-step count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.unstableForward.sourceRewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceRewriteStepCount
    triple

/-- Motive-root wrapper: the left-associated triple forward word keeps third target rewrite-step count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.unstableForward.targetRewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetRewriteStepCount
    triple

/-- Motive-root wrapper: the right-associated triple forward word keeps first source rewrite-step count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.unstableForward.sourceRewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceRewriteStepCount
    triple

/-- Motive-root wrapper: the right-associated triple forward word keeps third target rewrite-step count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.unstableForward.targetRewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetRewriteStepCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
