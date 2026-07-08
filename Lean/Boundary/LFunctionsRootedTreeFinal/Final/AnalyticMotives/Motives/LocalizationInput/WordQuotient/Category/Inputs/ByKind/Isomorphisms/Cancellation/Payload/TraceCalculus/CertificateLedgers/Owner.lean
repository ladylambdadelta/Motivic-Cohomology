import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.CertificateLedgers.Endpoints.Owner

/-!
# Combined certificate ledgers for named cancellation composites

This file specializes the generic input-cancellation endpoint-certificate
ledger facts to the six named localization-input constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation endpoint ledger is the doubled source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointCertificateLedger
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation endpoint ledger is the doubled target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointCertificateLedger
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation endpoint ledger is the doubled source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointCertificateLedger
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation endpoint ledger is the doubled target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointCertificateLedger
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation endpoint ledger is the doubled source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointCertificateLedger
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation endpoint ledger is the doubled target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointCertificateLedger
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation endpoint ledger is the doubled source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointCertificateLedger
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation endpoint ledger is the doubled target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointCertificateLedger
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation endpoint ledger is the doubled source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointCertificateLedger
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation endpoint ledger is the doubled target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointCertificateLedger
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation endpoint ledger is the doubled source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointCertificateLedger
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation endpoint ledger is the doubled target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointCertificateLedger
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
