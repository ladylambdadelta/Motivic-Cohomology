import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.TraceCalculus.CertificateLedgers.Owner

/-!
# Object-level payload of localized-arrow triple composites

This file identifies endpoint rectangle lists and certificate ledgers of the
two named localized-forward-arrow parenthesizations with the first source
object and third target object.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated localized-arrow source rectangles are the first source rectangles. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangles
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
      triple.first)

/-- The left-associated localized-arrow target rectangles are the third target rectangles. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangles
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
      triple.third)

/-- The right-associated localized-arrow source rectangles are the first source rectangles. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangles
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
      triple.first)

/-- The right-associated localized-arrow target rectangles are the third target rectangles. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangles
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
      triple.third)

/-- The left-associated localized-arrow source ledger is the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceCertificateLedger
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceCertificateLedger
      triple.first)

/-- The left-associated localized-arrow target ledger is the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetCertificateLedger
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetCertificateLedger
      triple.third)

/-- The right-associated localized-arrow source ledger is the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceCertificateLedger
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceCertificateLedger
      triple.first)

/-- The right-associated localized-arrow target ledger is the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetCertificateLedger
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetCertificateLedger
      triple.third)

end AnalyticMotives
end LFunctions
end Boundary
