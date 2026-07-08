import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.ObjectPayload.Owner

/-!
# Public object-level payload of triple forward words

This file exposes object-level rectangle-list and certificate-ledger payload
facts for unstable forward-word triple composites through the public root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated source rectangles are the first source rectangles. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    triple

/-- Public wrapper: left-associated target rectangles are the third target rectangles. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetObjectImportedRectangles
    triple

/-- Public wrapper: right-associated source rectangles are the first source rectangles. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    triple

/-- Public wrapper: right-associated target rectangles are the third target rectangles. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetObjectImportedRectangles
    triple

/-- Public wrapper: left-associated source ledger is the first source ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    triple

/-- Public wrapper: left-associated target ledger is the third target ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetObjectCertificateLedger
    triple

/-- Public wrapper: right-associated source ledger is the first source ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    triple

/-- Public wrapper: right-associated target ledger is the third target ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetObjectCertificateLedger
    triple

end AnalyticMotives
end LFunctions
end Boundary
