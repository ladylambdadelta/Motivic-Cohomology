import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectPayload.Owner

/-!
# Motive-root object-level payload of localized-arrow triple composites

This file exposes object-level rectangle-list and certificate-ledger payload
facts for localized-forward-arrow triple composites through the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated source rectangles are the first source rectangles. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    triple

/-- Motive-root wrapper: left-associated target rectangles are the third target rectangles. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    triple

/-- Motive-root wrapper: right-associated source rectangles are the first source rectangles. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    triple

/-- Motive-root wrapper: right-associated target rectangles are the third target rectangles. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    triple

/-- Motive-root wrapper: left-associated source ledger is the first source ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    triple

/-- Motive-root wrapper: left-associated target ledger is the third target ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    triple

/-- Motive-root wrapper: right-associated source ledger is the first source ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    triple

/-- Motive-root wrapper: right-associated target ledger is the third target ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    triple

end AnalyticMotives
end LFunctions
end Boundary
