import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Owner

/-!
# Public endpoint payload of localized-arrow triple composites

This file exposes endpoint rectangle and ledger projections for the two named
localized-forward-arrow triple composites through the public analytic-motives
root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated localized-arrow source rectangles. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.localizedForwardArrow.sourceImportedRectangles :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceImportedRectangles
    triple

/-- Public wrapper: left-associated localized-arrow target rectangles. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.localizedForwardArrow.targetImportedRectangles :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetImportedRectangles
    triple

/-- Public wrapper: right-associated localized-arrow source rectangles. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangles =
      triple.first.localizedForwardArrow.sourceImportedRectangles :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceImportedRectangles
    triple

/-- Public wrapper: right-associated localized-arrow target rectangles. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangles =
      triple.third.localizedForwardArrow.targetImportedRectangles :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetImportedRectangles
    triple

/-- Public wrapper: left-associated localized-arrow source ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.localizedForwardArrow.sourceCertificateLedger :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceCertificateLedger
    triple

/-- Public wrapper: left-associated localized-arrow target ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.localizedForwardArrow.targetCertificateLedger :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetCertificateLedger
    triple

/-- Public wrapper: right-associated localized-arrow source ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger =
      triple.first.localizedForwardArrow.sourceCertificateLedger :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceCertificateLedger
    triple

/-- Public wrapper: right-associated localized-arrow target ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger =
      triple.third.localizedForwardArrow.targetCertificateLedger :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetCertificateLedger
    triple

end AnalyticMotives
end LFunctions
end Boundary
