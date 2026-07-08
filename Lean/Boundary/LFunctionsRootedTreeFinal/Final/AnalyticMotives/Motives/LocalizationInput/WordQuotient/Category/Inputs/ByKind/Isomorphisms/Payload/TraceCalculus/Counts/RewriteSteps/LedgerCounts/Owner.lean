import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.RewriteSteps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.RewriteSteps.LedgerCounts.Endpoint.Owner

/-!
# Ledger-count facts for localized-isomorphism rewrite-step payload

This file exposes that endpoint rewrite-step counts on named localized
isomorphisms are counted by the corresponding endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism hom target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism hom source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism hom target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism hom source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism hom target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism hom source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism hom target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism hom source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism hom target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism hom source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism hom target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
