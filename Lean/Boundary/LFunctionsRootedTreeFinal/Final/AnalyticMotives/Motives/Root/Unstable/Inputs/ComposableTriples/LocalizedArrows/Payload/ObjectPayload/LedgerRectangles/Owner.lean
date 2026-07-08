import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectPayload.LedgerRectangles.Owner

/-!
# Motive-root object-level ledger rectangles of localized-arrow triple composites

This file exposes object-level ledger-rectangle facts for localized-forward-arrow
triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated source rectangles are extracted from the first source ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.certificateLedger.importedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    triple

/-- Motive-root wrapper: left-associated target rectangles are extracted from the third target ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.certificateLedger.importedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    triple

/-- Motive-root wrapper: right-associated source rectangles are extracted from the first source ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.certificateLedger.importedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    triple

/-- Motive-root wrapper: right-associated target rectangles are extracted from the third target ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.certificateLedger.importedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    triple

end AnalyticMotives
end LFunctions
end Boundary
