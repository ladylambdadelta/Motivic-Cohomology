import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectPayload.Owner

/-!
# Object-level ledger rectangles of localized-arrow triple composites

This file records that the object-level rectangle-list projections of the two
named localized-forward-arrow triple composites are extracted from the
corresponding endpoint object certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated source object rectangles are extracted from the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
      triple)
    (TraceCorQObject.importedRectangles_eq_certificateLedger_rectangles
      triple.first.sourceObject)

/-- The left-associated target object rectangles are extracted from the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
      triple)
    (TraceCorQObject.importedRectangles_eq_certificateLedger_rectangles
      triple.third.targetObject)

/-- The right-associated source object rectangles are extracted from the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.sourceObject.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceObjectImportedRectangles
      triple)
    (TraceCorQObject.importedRectangles_eq_certificateLedger_rectangles
      triple.first.sourceObject)

/-- The right-associated target object rectangles are extracted from the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles_eq_certificateLedger_rectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.targetObject.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetObjectImportedRectangles
      triple)
    (TraceCorQObject.importedRectangles_eq_certificateLedger_rectangles
      triple.third.targetObject)

end AnalyticMotives
end LFunctions
end Boundary
