import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.RewriteSteps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Endpoint rewrite-step ledger counts for named localized isomorphisms

This file owns endpoint rewrite-step count-as-ledger-count facts for the hom
and inverse arrows of the named localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelInverseArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
