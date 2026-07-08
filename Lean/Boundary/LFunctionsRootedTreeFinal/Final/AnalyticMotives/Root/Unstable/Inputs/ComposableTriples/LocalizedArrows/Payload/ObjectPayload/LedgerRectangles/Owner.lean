import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectPayload.LedgerRectangles.Owner

/-!
# Public object-level ledger rectangles of localized-arrow triple composites

This file exposes object-level ledger-rectangle facts for localized-forward-arrow
triple composites through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated source rectangles are extracted from the first source ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    triple

/-- Public wrapper: left-associated target rectangles are extracted from the third target ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    triple

/-- Public wrapper: right-associated source rectangles are extracted from the first source ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    triple

/-- Public wrapper: right-associated target rectangles are extracted from the third target ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    triple

end AnalyticMotives
end LFunctions
end Boundary
