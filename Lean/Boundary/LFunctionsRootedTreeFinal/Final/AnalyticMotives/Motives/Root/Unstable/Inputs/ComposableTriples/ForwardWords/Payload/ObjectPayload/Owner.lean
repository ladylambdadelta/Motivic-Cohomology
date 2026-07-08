import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.ObjectPayload.Owner

/-!
# Motive-root object-level payload of triple forward words

This file exposes object-level rectangle-list and certificate-ledger payload
facts for unstable forward-word triple composites through the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated source rectangles are the first source rectangles. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    triple

/-- Motive-root wrapper: left-associated target rectangles are the third target rectangles. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetObjectImportedRectangles
    triple

/-- Motive-root wrapper: right-associated source rectangles are the first source rectangles. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    triple

/-- Motive-root wrapper: right-associated target rectangles are the third target rectangles. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetObjectImportedRectangles
    triple

/-- Motive-root wrapper: left-associated source ledger is the first source ledger. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    triple

/-- Motive-root wrapper: left-associated target ledger is the third target ledger. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetObjectCertificateLedger
    triple

/-- Motive-root wrapper: right-associated source ledger is the first source ledger. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    triple

/-- Motive-root wrapper: right-associated target ledger is the third target ledger. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetObjectCertificateLedger
    triple

end AnalyticMotives
end LFunctions
end Boundary
