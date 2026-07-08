import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Associativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Endpoint.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.ObjectCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.ObjectPayload.Owner

/-!
# Public payload of triple forward words

This file exposes endpoint payload facts for the two parenthesizations of
unstable forward-word composites through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated unstable forward word composite. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord =
      TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord triple :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_eq
    triple

/-- Public wrapper: right-associated unstable forward word composite. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord =
      TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord triple :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_eq
    triple

/-- Public wrapper: the left-associated triple forward word keeps first source rectangles. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.unstableForward.sourceImportedRectangles :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceImportedRectangles
    triple

/-- Public wrapper: the left-associated triple forward word keeps third target rectangles. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.unstableForward.targetImportedRectangles :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetImportedRectangles
    triple

/-- Public wrapper: the right-associated triple forward word keeps first source rectangles. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.unstableForward.sourceImportedRectangles :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceImportedRectangles
    triple

/-- Public wrapper: the right-associated triple forward word keeps third target rectangles. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.unstableForward.targetImportedRectangles :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetImportedRectangles
    triple

/-- Public wrapper: the left-associated triple forward word keeps first source ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.unstableForward.sourceCertificateLedger :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceCertificateLedger
    triple

/-- Public wrapper: the left-associated triple forward word keeps third target ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.unstableForward.targetCertificateLedger :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetCertificateLedger
    triple

/-- Public wrapper: the right-associated triple forward word keeps first source ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.unstableForward.sourceCertificateLedger :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceCertificateLedger
    triple

/-- Public wrapper: the right-associated triple forward word keeps third target ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.unstableForward.targetCertificateLedger :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetCertificateLedger
    triple

/-- Public wrapper: the left-associated triple forward word keeps first source bookkeeping count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.unstableForward.sourceTraceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    triple

/-- Public wrapper: the left-associated triple forward word keeps third target bookkeeping count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.unstableForward.targetTraceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    triple

/-- Public wrapper: the right-associated triple forward word keeps first source bookkeeping count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.unstableForward.sourceTraceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    triple

/-- Public wrapper: the right-associated triple forward word keeps third target bookkeeping count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.unstableForward.targetTraceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    triple

/-- Public wrapper: the left-associated triple forward word keeps first source rewrite-step count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.unstableForward.sourceRewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceRewriteStepCount
    triple

/-- Public wrapper: the left-associated triple forward word keeps third target rewrite-step count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.unstableForward.targetRewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetRewriteStepCount
    triple

/-- Public wrapper: the right-associated triple forward word keeps first source rewrite-step count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.unstableForward.sourceRewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceRewriteStepCount
    triple

/-- Public wrapper: the right-associated triple forward word keeps third target rewrite-step count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.unstableForward.targetRewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetRewriteStepCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
