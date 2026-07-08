import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.TraceCalculus.Owner

/-!
# Trace-calculus counts for unstable localization-input isomorphisms

This file exposes trace-bookkeeping and rewrite-step counts for the hom and
inverse of each localization-input isomorphism after passage to the unstable
analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable isomorphism hom source bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_sourceTraceBookkeepingCount
    input

/-- The unstable isomorphism hom target bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.unstableIso_hom_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_targetTraceBookkeepingCount
    input

/-- The unstable isomorphism inverse source bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_sourceTraceBookkeepingCount
    input

/-- The unstable isomorphism inverse target bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.unstableIso_inv_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_targetTraceBookkeepingCount
    input

/-- The unstable isomorphism hom endpoint bookkeeping count is source plus target. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount +
        input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount
    input

/-- The unstable isomorphism inverse endpoint bookkeeping count is target plus source. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount +
        input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount
    input

/-- The unstable isomorphism hom source rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_sourceRewriteStepCount
    input

/-- The unstable isomorphism hom target rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.unstableIso_hom_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_targetRewriteStepCount
    input

/-- The unstable isomorphism inverse source rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_sourceRewriteStepCount
    input

/-- The unstable isomorphism inverse target rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.unstableIso_inv_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_targetRewriteStepCount
    input

/-- The unstable isomorphism hom endpoint rewrite-step count is source plus target. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointRewriteStepCount =
      input.sourceObject.rewriteStepCount +
        input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount
    input

/-- The unstable isomorphism inverse endpoint rewrite-step count is target plus source. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointRewriteStepCount =
      input.targetObject.rewriteStepCount +
        input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount
    input

end AnalyticMotives
end LFunctions
end Boundary
