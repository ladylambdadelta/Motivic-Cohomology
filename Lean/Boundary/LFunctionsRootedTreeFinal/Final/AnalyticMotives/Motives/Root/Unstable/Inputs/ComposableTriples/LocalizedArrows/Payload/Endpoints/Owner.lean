import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Owner

/-!
# Motive-root endpoint payload of localized-arrow triple composites

This file exposes endpoint rectangle and ledger projections for the two named
localized-forward-arrow triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated localized-arrow source rectangles. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.localizedForwardArrow.sourceImportedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangles
    triple

/-- Motive-root wrapper: left-associated localized-arrow target rectangles. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.localizedForwardArrow.targetImportedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangles
    triple

/-- Motive-root wrapper: right-associated localized-arrow source rectangles. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.localizedForwardArrow.sourceImportedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangles
    triple

/-- Motive-root wrapper: right-associated localized-arrow target rectangles. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.localizedForwardArrow.targetImportedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangles
    triple

/-- Motive-root wrapper: left-associated localized-arrow source ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.localizedForwardArrow.sourceCertificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceCertificateLedger
    triple

/-- Motive-root wrapper: left-associated localized-arrow target ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.localizedForwardArrow.targetCertificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetCertificateLedger
    triple

/-- Motive-root wrapper: right-associated localized-arrow source ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.localizedForwardArrow.sourceCertificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceCertificateLedger
    triple

/-- Motive-root wrapper: right-associated localized-arrow target ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.localizedForwardArrow.targetCertificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetCertificateLedger
    triple

end AnalyticMotives
end LFunctions
end Boundary
