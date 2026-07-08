import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.ArrowEndpoints.Owner

/-!
# Trace-calculus arrow endpoints for unstable named isomorphisms

This file exposes source and target certificate ledgers through the hom and
inverse arrows of the six named unstable analytic-motive localization
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom source ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceCertificateLedger
    source
    target

/-- Descent-channel unstable hom target ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_targetCertificateLedger
    source
    target

/-- Descent-channel unstable inverse source ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceCertificateLedger
    source
    target

/-- Descent-channel unstable inverse target ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_targetCertificateLedger
    source
    target

/-- Descent-refinement unstable hom source ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceCertificateLedger
    source
    target

/-- Descent-refinement unstable hom target ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetCertificateLedger
    source
    target

/-- Descent-refinement unstable inverse source ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceCertificateLedger
    source
    target

/-- Descent-refinement unstable inverse target ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetCertificateLedger
    source
    target

/-- Descent-schedule unstable hom source ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceCertificateLedger
    source
    target

/-- Descent-schedule unstable hom target ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetCertificateLedger
    source
    target

/-- Descent-schedule unstable inverse source ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceCertificateLedger
    source
    target

/-- Descent-schedule unstable inverse target ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetCertificateLedger
    source
    target

/-- Interval-Stokes unstable hom source ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceCertificateLedger
    source
    target

/-- Interval-Stokes unstable hom target ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetCertificateLedger
    source
    target

/-- Interval-Stokes unstable inverse source ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceCertificateLedger
    source
    target

/-- Interval-Stokes unstable inverse target ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetCertificateLedger
    source
    target

/-- Interval-Fubini unstable hom source ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceCertificateLedger
    source
    target

/-- Interval-Fubini unstable hom target ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetCertificateLedger
    source
    target

/-- Interval-Fubini unstable inverse source ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceCertificateLedger
    source
    target

/-- Interval-Fubini unstable inverse target ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetCertificateLedger
    source
    target

/-- Tate-weight-drop unstable hom source ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceCertificateLedger
    source
    target

/-- Tate-weight-drop unstable hom target ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetCertificateLedger
    source
    target

/-- Tate-weight-drop unstable inverse source ledger is the input target ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceCertificateLedger
    source
    target

/-- Tate-weight-drop unstable inverse target ledger is the input source ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetCertificateLedger
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
