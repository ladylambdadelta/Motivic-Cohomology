import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectPayload.Owner

/-!
# Public object-level payload of localized-arrow triple composites

This file exposes object-level rectangle-list and certificate-ledger payload
facts for localized-forward-arrow triple composites through the public
analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated source rectangles are the first source rectangles. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    triple

/-- Public wrapper: left-associated target rectangles are the third target rectangles. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    triple

/-- Public wrapper: right-associated source rectangles are the first source rectangles. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    triple

/-- Public wrapper: right-associated target rectangles are the third target rectangles. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    triple

/-- Public wrapper: left-associated source ledger is the first source ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    triple

/-- Public wrapper: left-associated target ledger is the third target ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    triple

/-- Public wrapper: right-associated source ledger is the first source ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    triple

/-- Public wrapper: right-associated target ledger is the third target ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    triple

end AnalyticMotives
end LFunctions
end Boundary
