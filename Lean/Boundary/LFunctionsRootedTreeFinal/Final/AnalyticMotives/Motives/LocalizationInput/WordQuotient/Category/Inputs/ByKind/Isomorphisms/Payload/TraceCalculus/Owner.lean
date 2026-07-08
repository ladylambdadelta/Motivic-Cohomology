import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.ArrowEndpoints.Owner

/-!
# Trace-calculus payload for named localized isomorphisms

This file exposes concatenated endpoint certificate ledgers through the hom and
inverse arrows of the named by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom endpoint ledger appends source and target ledgers. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso source target).hom.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger
        (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_hom_endpointCertificateLedger
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel isomorphism inverse endpoint ledger appends target and source ledgers. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso source target).inv.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger
        (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_inv_endpointCertificateLedger
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement isomorphism hom endpoint ledger appends source and target ledgers. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger
        (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_hom_endpointCertificateLedger
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement isomorphism inverse endpoint ledger appends target and source ledgers. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger
        (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_inv_endpointCertificateLedger
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule isomorphism hom endpoint ledger appends source and target ledgers. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger
        (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_hom_endpointCertificateLedger
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule isomorphism inverse endpoint ledger appends target and source ledgers. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger
        (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_inv_endpointCertificateLedger
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes isomorphism hom endpoint ledger appends source and target ledgers. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger
        (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_hom_endpointCertificateLedger
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes isomorphism inverse endpoint ledger appends target and source ledgers. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger
        (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_inv_endpointCertificateLedger
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini isomorphism hom endpoint ledger appends source and target ledgers. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger
        (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_hom_endpointCertificateLedger
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini isomorphism inverse endpoint ledger appends target and source ledgers. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger
        (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_inv_endpointCertificateLedger
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop isomorphism hom endpoint ledger appends source and target ledgers. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_hom_endpointCertificateLedger
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop isomorphism inverse endpoint ledger appends target and source ledgers. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedWordIso_inv_endpointCertificateLedger
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
