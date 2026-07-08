import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.TraceCalculus.Owner

/-!
# Endpoint certificate ledgers for named cancellation composites

This file specializes the generic input-cancellation source and target
certificate-ledger facts to the six named localization-input constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoHomInv.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceCertificateLedger
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoHomInv.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetCertificateLedger
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoInvHom.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceCertificateLedger
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoInvHom.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetCertificateLedger
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoHomInv.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceCertificateLedger
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoHomInv.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetCertificateLedger
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoInvHom.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceCertificateLedger
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoInvHom.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetCertificateLedger
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoHomInv.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceCertificateLedger
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoHomInv.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetCertificateLedger
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoInvHom.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceCertificateLedger
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoInvHom.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetCertificateLedger
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoHomInv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceCertificateLedger
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoHomInv.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetCertificateLedger
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoInvHom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceCertificateLedger
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoInvHom.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetCertificateLedger
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoHomInv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceCertificateLedger
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoHomInv.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetCertificateLedger
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoInvHom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceCertificateLedger
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoInvHom.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetCertificateLedger
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation source ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoHomInv.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceCertificateLedger
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop hom-inverse cancellation target ledger is the source endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoHomInv.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetCertificateLedger
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation source ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoInvHom.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceCertificateLedger
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation target ledger is the target endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoInvHom.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetCertificateLedger
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
