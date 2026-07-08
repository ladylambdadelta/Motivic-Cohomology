import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.Owner

/-!
# Composition trace-calculus payload in the unstable envelope

This file exposes endpoint certificate-ledger, trace-bookkeeping, and
rewrite-step payload for composition of unstable analytic-motive homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition keeps the left hom source endpoint bookkeeping payload. -/
theorem TraceUnstableAnalyticMotiveHom.comp_sourceTraceBookkeepingCount
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).sourceTraceBookkeepingCount =
      TraceLocalizedWordHom.sourceTraceBookkeepingCount left :=
  TraceLocalizedWordHom.comp_sourceTraceBookkeepingCount
    left
    right

/-- Composition keeps the right hom target endpoint bookkeeping payload. -/
theorem TraceUnstableAnalyticMotiveHom.comp_targetTraceBookkeepingCount
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).targetTraceBookkeepingCount =
      TraceLocalizedWordHom.targetTraceBookkeepingCount right :=
  TraceLocalizedWordHom.comp_targetTraceBookkeepingCount
    left
    right

/-- Composition keeps the left hom source endpoint rewrite-step payload. -/
theorem TraceUnstableAnalyticMotiveHom.comp_sourceRewriteStepCount
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).sourceRewriteStepCount =
      TraceLocalizedWordHom.sourceRewriteStepCount left :=
  TraceLocalizedWordHom.comp_sourceRewriteStepCount
    left
    right

/-- Composition keeps the right hom target endpoint rewrite-step payload. -/
theorem TraceUnstableAnalyticMotiveHom.comp_targetRewriteStepCount
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).targetRewriteStepCount =
      TraceLocalizedWordHom.targetRewriteStepCount right :=
  TraceLocalizedWordHom.comp_targetRewriteStepCount
    left
    right

/-- Composition keeps the left hom source endpoint certificate ledger. -/
theorem TraceUnstableAnalyticMotiveHom.comp_sourceCertificateLedger
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).sourceCertificateLedger =
      TraceLocalizedWordHom.sourceCertificateLedger left :=
  TraceLocalizedWordHom.comp_sourceCertificateLedger
    left
    right

/-- Composition keeps the right hom target endpoint certificate ledger. -/
theorem TraceUnstableAnalyticMotiveHom.comp_targetCertificateLedger
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).targetCertificateLedger =
      TraceLocalizedWordHom.targetCertificateLedger right :=
  TraceLocalizedWordHom.comp_targetCertificateLedger
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
