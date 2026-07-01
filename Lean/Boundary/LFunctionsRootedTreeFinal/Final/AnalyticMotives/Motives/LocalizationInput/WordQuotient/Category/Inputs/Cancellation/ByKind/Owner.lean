import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Owner

/-!
# Named cancellation laws by localization-input kind

This file exposes forward-inverse and inverse-forward cancellation laws for
each concrete localization-input constructor.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward followed by inverse is identity. -/
theorem TraceLocalizationInput.descentChannelForward_comp_inverse
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelForwardArrow source target)
        (TraceLocalizationInput.descentChannelInverseArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).sourceObject :=
  TraceLocalizationInput.localizedForward_comp_inverse
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse followed by forward is identity. -/
theorem TraceLocalizationInput.descentChannelInverse_comp_forward
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelInverseArrow source target)
        (TraceLocalizationInput.descentChannelForwardArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).targetObject :=
  TraceLocalizationInput.localizedInverse_comp_forward
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward followed by inverse is identity. -/
theorem TraceLocalizationInput.descentRefinementForward_comp_inverse
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementForwardArrow source target)
        (TraceLocalizationInput.descentRefinementInverseArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).sourceObject :=
  TraceLocalizationInput.localizedForward_comp_inverse
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse followed by forward is identity. -/
theorem TraceLocalizationInput.descentRefinementInverse_comp_forward
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementInverseArrow source target)
        (TraceLocalizationInput.descentRefinementForwardArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).targetObject :=
  TraceLocalizationInput.localizedInverse_comp_forward
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward followed by inverse is identity. -/
theorem TraceLocalizationInput.descentScheduleForward_comp_inverse
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleForwardArrow source target)
        (TraceLocalizationInput.descentScheduleInverseArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).sourceObject :=
  TraceLocalizationInput.localizedForward_comp_inverse
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse followed by forward is identity. -/
theorem TraceLocalizationInput.descentScheduleInverse_comp_forward
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleInverseArrow source target)
        (TraceLocalizationInput.descentScheduleForwardArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).targetObject :=
  TraceLocalizationInput.localizedInverse_comp_forward
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward followed by inverse is identity. -/
theorem TraceLocalizationInput.intervalStokesForward_comp_inverse
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesForwardArrow source target)
        (TraceLocalizationInput.intervalStokesInverseArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).sourceObject :=
  TraceLocalizationInput.localizedForward_comp_inverse
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse followed by forward is identity. -/
theorem TraceLocalizationInput.intervalStokesInverse_comp_forward
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesInverseArrow source target)
        (TraceLocalizationInput.intervalStokesForwardArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).targetObject :=
  TraceLocalizationInput.localizedInverse_comp_forward
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward followed by inverse is identity. -/
theorem TraceLocalizationInput.intervalFubiniForward_comp_inverse
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniForwardArrow source target)
        (TraceLocalizationInput.intervalFubiniInverseArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceLocalizationInput.localizedForward_comp_inverse
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse followed by forward is identity. -/
theorem TraceLocalizationInput.intervalFubiniInverse_comp_forward
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniInverseArrow source target)
        (TraceLocalizationInput.intervalFubiniForwardArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceLocalizationInput.localizedInverse_comp_forward
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward followed by inverse is identity. -/
theorem TraceLocalizationInput.tateWeightDropForward_comp_inverse
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropForwardArrow source target)
        (TraceLocalizationInput.tateWeightDropInverseArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceLocalizationInput.localizedForward_comp_inverse
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse followed by forward is identity. -/
theorem TraceLocalizationInput.tateWeightDropInverse_comp_forward
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropInverseArrow source target)
        (TraceLocalizationInput.tateWeightDropForwardArrow source target) =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceLocalizationInput.localizedInverse_comp_forward
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
