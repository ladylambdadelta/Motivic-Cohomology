import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Owner

/-!
# Object-level payload of triple forward words

This file identifies endpoint rectangle lists and certificate ledgers of the
two unstable forward-word parenthesizations with the first source object and
third target object.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated triple forward word source rectangles are the first source rectangles. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceImportedRectangles
      triple)
    (TraceLocalizationInput.unstableForward_sourceImportedRectangles
      triple.first)

/-- The left-associated triple forward word target rectangles are the third target rectangles. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetImportedRectangles
      triple)
    (TraceLocalizationInput.unstableForward_targetImportedRectangles
      triple.third)

/-- The right-associated triple forward word source rectangles are the first source rectangles. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.sourceObject.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceImportedRectangles
      triple)
    (TraceLocalizationInput.unstableForward_sourceImportedRectangles
      triple.first)

/-- The right-associated triple forward word target rectangles are the third target rectangles. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetObjectImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.targetObject.importedRectangles :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetImportedRectangles
      triple)
    (TraceLocalizationInput.unstableForward_targetImportedRectangles
      triple.third)

/-- The left-associated triple forward word source ledger is the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceCertificateLedger
      triple)
    (TraceLocalizationInput.unstableForward_sourceCertificateLedger
      triple.first)

/-- The left-associated triple forward word target ledger is the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetCertificateLedger
      triple)
    (TraceLocalizationInput.unstableForward_targetCertificateLedger
      triple.third)

/-- The right-associated triple forward word source ledger is the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.sourceObject.certificateLedger :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceCertificateLedger
      triple)
    (TraceLocalizationInput.unstableForward_sourceCertificateLedger
      triple.first)

/-- The right-associated triple forward word target ledger is the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetObjectCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.targetObject.certificateLedger :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetCertificateLedger
      triple)
    (TraceLocalizationInput.unstableForward_targetCertificateLedger
      triple.third)

end AnalyticMotives
end LFunctions
end Boundary
