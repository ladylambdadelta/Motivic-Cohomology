import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.Bookkeeping.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.Bookkeeping.LedgerCounts.Endpoint.Owner

/-!
# Ledger-count facts for localized-isomorphism bookkeeping payload

This file exposes that endpoint trace-bookkeeping counts on named localized
isomorphisms are counted by the corresponding endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism hom target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism hom source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism hom target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism hom source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism hom target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism hom source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism hom target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism hom source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism hom target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism hom source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism hom target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
