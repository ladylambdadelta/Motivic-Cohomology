import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Payload.TraceCalculus.Owner

/-!
# Endpoint payload of localized-arrow triple composites

This file records the endpoint payload carried by the two named
localized-forward-arrow triple composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated localized-arrow composite keeps the first source rectangles. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.localizedForwardArrow.sourceImportedRectangles :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceImportedRectangles
              (TraceLocalizationWordClass.comp
                triple.first.localizedForwardArrow
                triple.second.localizedForwardArrow)
              triple.third.localizedForwardArrow)
            (TraceLocalizationWordClass.comp_sourceImportedRectangles
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)

/-- The left-associated localized-arrow composite keeps the third target rectangles. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.localizedForwardArrow.targetImportedRectangles :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_targetImportedRectangles
            (TraceLocalizationWordClass.comp
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)
            triple.third.localizedForwardArrow

/-- The right-associated localized-arrow composite keeps the first source rectangles. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.localizedForwardArrow.sourceImportedRectangles :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_sourceImportedRectangles
            triple.first.localizedForwardArrow
            (TraceLocalizationWordClass.comp
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

/-- The right-associated localized-arrow composite keeps the third target rectangles. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.localizedForwardArrow.targetImportedRectangles :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetImportedRectangles
              triple.first.localizedForwardArrow
              (TraceLocalizationWordClass.comp
                triple.second.localizedForwardArrow
                triple.third.localizedForwardArrow))
            (TraceLocalizationWordClass.comp_targetImportedRectangles
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

/-- The left-associated localized-arrow composite keeps the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.localizedForwardArrow.sourceCertificateLedger :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceCertificateLedger
              (TraceLocalizationWordClass.comp
                triple.first.localizedForwardArrow
                triple.second.localizedForwardArrow)
              triple.third.localizedForwardArrow)
            (TraceLocalizationWordClass.comp_sourceCertificateLedger
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)

/-- The left-associated localized-arrow composite keeps the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.localizedForwardArrow.targetCertificateLedger :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_targetCertificateLedger
            (TraceLocalizationWordClass.comp
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)
            triple.third.localizedForwardArrow

/-- The right-associated localized-arrow composite keeps the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.localizedForwardArrow.sourceCertificateLedger :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_sourceCertificateLedger
            triple.first.localizedForwardArrow
            (TraceLocalizationWordClass.comp
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

/-- The right-associated localized-arrow composite keeps the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.localizedForwardArrow.targetCertificateLedger :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetCertificateLedger
              triple.first.localizedForwardArrow
              (TraceLocalizationWordClass.comp
                triple.second.localizedForwardArrow
                triple.third.localizedForwardArrow))
            (TraceLocalizationWordClass.comp_targetCertificateLedger
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

end AnalyticMotives
end LFunctions
end Boundary
