import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Arrows.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.Counts.Owner

/-!
# Trace-calculus arrow-endpoint payload for named localized isomorphisms

This file exposes source and target certificate ledgers through the hom and
inverse arrows of the named by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source ledger is the input source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceCertificateLedger
    source
    target

/-- Descent-channel isomorphism hom target ledger is the input target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentChannelForwardArrow_targetCertificateLedger
    source
    target

/-- Descent-channel isomorphism inverse source ledger is the input target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceCertificateLedger
    source
    target

/-- Descent-channel isomorphism inverse target ledger is the input source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentChannelInverseArrow_targetCertificateLedger
    source
    target

/-- Descent-refinement isomorphism hom source ledger is the input source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceCertificateLedger
    source
    target

/-- Descent-refinement isomorphism hom target ledger is the input target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetCertificateLedger
    source
    target

/-- Descent-refinement isomorphism inverse source ledger is the input target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceCertificateLedger
    source
    target

/-- Descent-refinement isomorphism inverse target ledger is the input source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetCertificateLedger
    source
    target

/-- Descent-schedule isomorphism hom source ledger is the input source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceCertificateLedger
    source
    target

/-- Descent-schedule isomorphism hom target ledger is the input target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetCertificateLedger
    source
    target

/-- Descent-schedule isomorphism inverse source ledger is the input target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceCertificateLedger
    source
    target

/-- Descent-schedule isomorphism inverse target ledger is the input source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetCertificateLedger
    source
    target

/-- Interval-Stokes isomorphism hom source ledger is the input source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceCertificateLedger
    source
    target

/-- Interval-Stokes isomorphism hom target ledger is the input target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetCertificateLedger
    source
    target

/-- Interval-Stokes isomorphism inverse source ledger is the input target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceCertificateLedger
    source
    target

/-- Interval-Stokes isomorphism inverse target ledger is the input source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetCertificateLedger
    source
    target

/-- Interval-Fubini isomorphism hom source ledger is the input source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceCertificateLedger
    source
    target

/-- Interval-Fubini isomorphism hom target ledger is the input target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetCertificateLedger
    source
    target

/-- Interval-Fubini isomorphism inverse source ledger is the input target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceCertificateLedger
    source
    target

/-- Interval-Fubini isomorphism inverse target ledger is the input source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetCertificateLedger
    source
    target

/-- Tate-weight-drop isomorphism hom source ledger is the input source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceCertificateLedger
    source
    target

/-- Tate-weight-drop isomorphism hom target ledger is the input target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetCertificateLedger
    source
    target

/-- Tate-weight-drop isomorphism inverse source ledger is the input target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceCertificateLedger
    source
    target

/-- Tate-weight-drop isomorphism inverse target ledger is the input source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetCertificateLedger
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
