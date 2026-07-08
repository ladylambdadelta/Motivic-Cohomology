import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.Owner

/-!
# Identity trace-calculus payload in the unstable envelope

This file exposes endpoint certificate-ledger, trace-bookkeeping, and
rewrite-step payload for identity homs in the unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity hom source endpoint bookkeeping is the object's bookkeeping payload. -/
theorem TraceUnstableAnalyticMotiveHom.id_sourceTraceBookkeepingCount
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).sourceTraceBookkeepingCount =
      TraceLocalizedWordObject.traceBookkeepingCount object :=
  TraceLocalizedWordHom.id_sourceTraceBookkeepingCount
    object

/-- Identity hom target endpoint bookkeeping is the object's bookkeeping payload. -/
theorem TraceUnstableAnalyticMotiveHom.id_targetTraceBookkeepingCount
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).targetTraceBookkeepingCount =
      TraceLocalizedWordObject.traceBookkeepingCount object :=
  TraceLocalizedWordHom.id_targetTraceBookkeepingCount
    object

/-- Identity hom source endpoint rewrite-step count is the object's rewrite payload. -/
theorem TraceUnstableAnalyticMotiveHom.id_sourceRewriteStepCount
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).sourceRewriteStepCount =
      TraceLocalizedWordObject.rewriteStepCount object :=
  TraceLocalizedWordHom.id_sourceRewriteStepCount
    object

/-- Identity hom target endpoint rewrite-step count is the object's rewrite payload. -/
theorem TraceUnstableAnalyticMotiveHom.id_targetRewriteStepCount
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).targetRewriteStepCount =
      TraceLocalizedWordObject.rewriteStepCount object :=
  TraceLocalizedWordHom.id_targetRewriteStepCount
    object

/-- Identity hom source endpoint ledger is the object's certificate ledger. -/
theorem TraceUnstableAnalyticMotiveHom.id_sourceCertificateLedger
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).sourceCertificateLedger =
      TraceLocalizedWordObject.certificateLedger object :=
  TraceLocalizedWordHom.id_sourceCertificateLedger
    object

/-- Identity hom target endpoint ledger is the object's certificate ledger. -/
theorem TraceUnstableAnalyticMotiveHom.id_targetCertificateLedger
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).targetCertificateLedger =
      TraceLocalizedWordObject.certificateLedger object :=
  TraceLocalizedWordHom.id_targetCertificateLedger
    object

end AnalyticMotives
end LFunctions
end Boundary
