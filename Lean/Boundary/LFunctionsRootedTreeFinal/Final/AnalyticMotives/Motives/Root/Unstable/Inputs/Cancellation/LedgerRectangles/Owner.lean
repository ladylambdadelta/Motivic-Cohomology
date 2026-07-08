import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.ImportedRectangles.LedgerRectangles.Owner

/-!
# Motive-root cancellation imported-rectangle ledger lists

This file exposes endpoint imported-rectangle list-as-ledger-list facts for
hom-inverse and inverse-hom cancellation composites of all six named unstable
localization isomorphisms at the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-channel inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-refinement hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-refinement inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-schedule hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-schedule inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind interval-Stokes hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind interval-Stokes inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind interval-Fubini hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind interval-Fubini inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind Tate-weight-drop hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind Tate-weight-drop inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
