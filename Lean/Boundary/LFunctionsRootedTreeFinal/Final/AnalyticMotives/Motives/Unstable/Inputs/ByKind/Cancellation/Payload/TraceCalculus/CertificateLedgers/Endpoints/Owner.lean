import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.CertificateLedgers.Endpoints.Owner

/-!
# Endpoint certificate ledgers for unstable cancellation composites

This file exposes source and target certificate-ledger identities for the
cancellation composites of the six named unstable analytic-motive localization
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Descent-channel unstable hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Descent-channel unstable inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Descent-channel unstable inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Descent-refinement unstable hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Descent-refinement unstable hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Descent-refinement unstable inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Descent-refinement unstable inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Descent-schedule unstable hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Descent-schedule unstable hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Descent-schedule unstable inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Descent-schedule unstable inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Interval-Stokes unstable hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Interval-Stokes unstable hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Interval-Stokes unstable inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Interval-Stokes unstable inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_targetCertificateLedger
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
