import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.Representatives.Owner

/-!
# Top-root localization representative wrappers

This file exposes the chosen one-atom word representatives for localized
calculus isomorphism arrows under the top-level `AnalyticMotivesRoot`
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The descent-channel hom has a one-atom representative. -/
theorem AnalyticMotivesRoot.descentChannelIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentChannelIso_hom_representative_atomCount
    source
    target

/-- The descent-channel inverse has a one-atom representative. -/
theorem AnalyticMotivesRoot.descentChannelIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentChannelIso_inv_representative_atomCount
    source
    target

/-- The descent-refinement hom has a one-atom representative. -/
theorem AnalyticMotivesRoot.descentRefinementIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentRefinementIso_hom_representative_atomCount
    source
    target

/-- The descent-refinement inverse has a one-atom representative. -/
theorem AnalyticMotivesRoot.descentRefinementIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentRefinementIso_inv_representative_atomCount
    source
    target

/-- The descent-schedule hom has a one-atom representative. -/
theorem AnalyticMotivesRoot.descentScheduleIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentScheduleIso_hom_representative_atomCount
    source
    target

/-- The descent-schedule inverse has a one-atom representative. -/
theorem AnalyticMotivesRoot.descentScheduleIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentScheduleIso_inv_representative_atomCount
    source
    target

/-- The interval-Stokes hom has a one-atom representative. -/
theorem AnalyticMotivesRoot.intervalStokesIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalStokesIso_hom_representative_atomCount
    source
    target

/-- The interval-Stokes inverse has a one-atom representative. -/
theorem AnalyticMotivesRoot.intervalStokesIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalStokesIso_inv_representative_atomCount
    source
    target

/-- The interval-Fubini hom has a one-atom representative. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalFubiniIso_hom_representative_atomCount
    source
    target

/-- The interval-Fubini inverse has a one-atom representative. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalFubiniIso_inv_representative_atomCount
    source
    target

/-- The Tate weight-drop hom has a one-atom representative. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_hom_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.tateWeightDrop source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.tateWeightDropIso_hom_representative_atomCount
    source
    target

/-- The Tate weight-drop inverse has a one-atom representative. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_inv_representative_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.tateWeightDrop source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.tateWeightDropIso_inv_representative_atomCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
