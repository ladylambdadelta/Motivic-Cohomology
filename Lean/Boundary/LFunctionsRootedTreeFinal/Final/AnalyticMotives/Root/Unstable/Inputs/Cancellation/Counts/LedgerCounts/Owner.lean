import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.Counts.LedgerCounts.Owner

/-!
# Top-root all-kind unstable cancellation endpoint ledger counts

This file mirrors endpoint imported-rectangle count-as-certificate-ledger-count
facts for all six named unstable localization cancellation composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom-inverse count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-channel inverse-hom count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement hom-inverse count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement inverse-hom count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule hom-inverse count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule inverse-hom count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes hom-inverse count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes inverse-hom count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini hom-inverse count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini inverse-hom count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom-inverse count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse-hom count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
