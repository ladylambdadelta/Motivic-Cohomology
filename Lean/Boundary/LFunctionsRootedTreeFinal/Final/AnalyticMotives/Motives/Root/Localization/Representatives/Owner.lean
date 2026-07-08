import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Descent.Localization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.IntervalHomotopy.Localization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.TateStabilization.Localization.Owner

/-!
# Motive-root localization representative wrappers

This file exposes the chosen one-atom word representatives for the localized
descent, interval, and Tate calculus isomorphism arrows.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The descent-channel hom has a one-atom representative. -/
theorem TraceAnalyticMotive.descentChannelIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceDescentLocalization.channelIso_hom_representative_atomCount
    source
    target

/-- The descent-channel inverse has a one-atom representative. -/
theorem TraceAnalyticMotive.descentChannelIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceDescentLocalization.channelIso_inv_representative_atomCount
    source
    target

/-- The descent-refinement hom has a one-atom representative. -/
theorem TraceAnalyticMotive.descentRefinementIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  TraceDescentLocalization.refinementIso_hom_representative_atomCount
    source
    target

/-- The descent-refinement inverse has a one-atom representative. -/
theorem TraceAnalyticMotive.descentRefinementIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  TraceDescentLocalization.refinementIso_inv_representative_atomCount
    source
    target

/-- The descent-schedule hom has a one-atom representative. -/
theorem TraceAnalyticMotive.descentScheduleIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  TraceDescentLocalization.scheduleIso_hom_representative_atomCount
    source
    target

/-- The descent-schedule inverse has a one-atom representative. -/
theorem TraceAnalyticMotive.descentScheduleIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  TraceDescentLocalization.scheduleIso_inv_representative_atomCount
    source
    target

/-- The interval-Stokes hom has a one-atom representative. -/
theorem TraceAnalyticMotive.intervalStokesIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  TraceIntervalHomotopyLocalization.stokesIso_hom_representative_atomCount
    source
    target

/-- The interval-Stokes inverse has a one-atom representative. -/
theorem TraceAnalyticMotive.intervalStokesIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  TraceIntervalHomotopyLocalization.stokesIso_inv_representative_atomCount
    source
    target

/-- The interval-Fubini hom has a one-atom representative. -/
theorem TraceAnalyticMotive.intervalFubiniIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  TraceIntervalHomotopyLocalization.fubiniIso_hom_representative_atomCount
    source
    target

/-- The interval-Fubini inverse has a one-atom representative. -/
theorem TraceAnalyticMotive.intervalFubiniIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  TraceIntervalHomotopyLocalization.fubiniIso_inv_representative_atomCount
    source
    target

/-- The Tate weight-drop hom has a one-atom representative. -/
theorem TraceAnalyticMotive.tateWeightDropIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.tateWeightDrop source target)).atomCount =
      0 + 1 :=
  TraceTateStabilizationLocalization.weightDropIso_hom_representative_atomCount
    source
    target

/-- The Tate weight-drop inverse has a one-atom representative. -/
theorem TraceAnalyticMotive.tateWeightDropIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.tateWeightDrop source target)).atomCount =
      0 + 1 :=
  TraceTateStabilizationLocalization.weightDropIso_inv_representative_atomCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
