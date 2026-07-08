import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.Representatives.Owner

/-!
# Motive-root localization representative summaries

This file exposes one-atom representative count summaries for the six calculus
localization isomorphism hom and inverse arrows.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Localization aggregate: descent-channel hom is represented by a one-atom word. -/
theorem TraceAnalyticMotive.descentChannelIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentChannelIso_hom_representative_atomCount
    source
    target

/-- Localization aggregate: descent-channel inverse is represented by a one-atom word. -/
theorem TraceAnalyticMotive.descentChannelIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentChannelIso_inv_representative_atomCount
    source
    target

/-- Localization aggregate: descent-refinement hom is represented by a one-atom word. -/
theorem TraceAnalyticMotive.descentRefinementIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentRefinementIso_hom_representative_atomCount
    source
    target

/-- Localization aggregate: descent-refinement inverse is represented by a one-atom word. -/
theorem TraceAnalyticMotive.descentRefinementIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentRefinementIso_inv_representative_atomCount
    source
    target

/-- Localization aggregate: descent-schedule hom is represented by a one-atom word. -/
theorem TraceAnalyticMotive.descentScheduleIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentScheduleIso_hom_representative_atomCount
    source
    target

/-- Localization aggregate: descent-schedule inverse is represented by a one-atom word. -/
theorem TraceAnalyticMotive.descentScheduleIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentScheduleIso_inv_representative_atomCount
    source
    target

/-- Localization aggregate: interval-Stokes hom is represented by a one-atom word. -/
theorem TraceAnalyticMotive.intervalStokesIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalStokesIso_hom_representative_atomCount
    source
    target

/-- Localization aggregate: interval-Stokes inverse is represented by a one-atom word. -/
theorem TraceAnalyticMotive.intervalStokesIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalStokesIso_inv_representative_atomCount
    source
    target

/-- Localization aggregate: interval-Fubini hom is represented by a one-atom word. -/
theorem TraceAnalyticMotive.intervalFubiniIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalFubiniIso_hom_representative_atomCount
    source
    target

/-- Localization aggregate: interval-Fubini inverse is represented by a one-atom word. -/
theorem TraceAnalyticMotive.intervalFubiniIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalFubiniIso_inv_representative_atomCount
    source
    target

/-- Localization aggregate: Tate weight-drop hom is represented by a one-atom word. -/
theorem TraceAnalyticMotive.tateWeightDropIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.tateWeightDrop source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.tateWeightDropIso_hom_representative_atomCount
    source
    target

/-- Localization aggregate: Tate weight-drop inverse is represented by a one-atom word. -/
theorem TraceAnalyticMotive.tateWeightDropIso_inv_localizationSummary_atomCount
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
