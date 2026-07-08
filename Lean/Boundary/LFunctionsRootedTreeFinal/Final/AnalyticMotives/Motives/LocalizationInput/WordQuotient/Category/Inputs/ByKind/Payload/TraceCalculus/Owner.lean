import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.TraceCalculus.Owner

/-!
# Trace-calculus payload for named input arrows by kind

This file specializes endpoint certificate-ledger payload for each named
localization-input forward and inverse arrow.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward arrow source ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Descent-channel forward arrow target ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.descentChannel
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Descent-channel inverse arrow source ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Descent-channel inverse arrow target ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.descentChannel
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Descent-refinement forward arrow source ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Descent-refinement forward arrow target ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Descent-refinement inverse arrow source ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Descent-refinement inverse arrow target ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Descent-schedule forward arrow source ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Descent-schedule forward arrow target ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Descent-schedule inverse arrow source ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Descent-schedule inverse arrow target ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Interval-Stokes forward arrow source ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Interval-Stokes forward arrow target ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Interval-Stokes inverse arrow source ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Interval-Stokes inverse arrow target ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Interval-Fubini forward arrow source ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Interval-Fubini forward arrow target ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Interval-Fubini inverse arrow source ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Interval-Fubini inverse arrow target ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Tate-weight-drop forward arrow source ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).sourceObject.certificateLedger :=
  rfl

/-- Tate-weight-drop forward arrow target ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Tate-weight-drop inverse arrow source ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).targetObject.certificateLedger :=
  rfl

/-- Tate-weight-drop inverse arrow target ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).sourceObject.certificateLedger :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
