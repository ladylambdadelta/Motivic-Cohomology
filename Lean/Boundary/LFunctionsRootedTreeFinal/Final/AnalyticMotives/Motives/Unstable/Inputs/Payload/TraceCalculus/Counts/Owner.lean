import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.TraceCalculus.Owner

/-!
# Trace-calculus counts for unstable localization-input arrows

This file exposes trace-bookkeeping and rewrite-step count identities for
localization input arrows after they are viewed as morphisms in the unstable
analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable forward source bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.unstableForward_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount
    input

/-- The unstable forward target bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.unstableForward_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableForward.targetTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount
    input

/-- The unstable inverse source bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.unstableInverse_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount
    input

/-- The unstable inverse target bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.unstableInverse_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount
    input

/-- The unstable forward endpoint bookkeeping count is source plus target. -/
theorem TraceLocalizationInput.unstableForward_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount +
        input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointTraceBookkeepingCount
    input

/-- The unstable inverse endpoint bookkeeping count is target plus source. -/
theorem TraceLocalizationInput.unstableInverse_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount +
        input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointTraceBookkeepingCount
    input

/-- The unstable forward source rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.unstableForward_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount
    input

/-- The unstable forward target rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.unstableForward_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableForward.targetRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount
    input

/-- The unstable inverse source rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.unstableInverse_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount
    input

/-- The unstable inverse target rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.unstableInverse_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount
    input

/-- The unstable forward endpoint rewrite-step count is source plus target. -/
theorem TraceLocalizationInput.unstableForward_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointRewriteStepCount =
      input.sourceObject.rewriteStepCount +
        input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointRewriteStepCount
    input

/-- The unstable inverse endpoint rewrite-step count is target plus source. -/
theorem TraceLocalizationInput.unstableInverse_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointRewriteStepCount =
      input.targetObject.rewriteStepCount +
        input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointRewriteStepCount
    input

end AnalyticMotives
end LFunctions
end Boundary
