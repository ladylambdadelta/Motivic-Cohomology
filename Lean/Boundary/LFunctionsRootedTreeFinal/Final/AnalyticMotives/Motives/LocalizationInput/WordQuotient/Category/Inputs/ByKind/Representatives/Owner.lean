import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Owner

/-!
# Chosen representatives for named localization-input arrows

This file records the chosen one-atom word representatives for each named
by-kind localized forward and inverse arrow.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The descent-channel forward arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  rfl

/-- The descent-channel inverse arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  rfl

/-- The descent-refinement forward arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  rfl

/-- The descent-refinement inverse arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  rfl

/-- The descent-schedule forward arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  rfl

/-- The descent-schedule inverse arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  rfl

/-- The interval-Stokes forward arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  rfl

/-- The interval-Stokes inverse arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  rfl

/-- The interval-Fubini forward arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  rfl

/-- The interval-Fubini inverse arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  rfl

/-- The Tate-weight-drop forward arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.tateWeightDrop source target)).atomCount =
      0 + 1 :=
  rfl

/-- The Tate-weight-drop inverse arrow has a one-atom chosen representative. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.tateWeightDrop source target)).atomCount =
      0 + 1 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
