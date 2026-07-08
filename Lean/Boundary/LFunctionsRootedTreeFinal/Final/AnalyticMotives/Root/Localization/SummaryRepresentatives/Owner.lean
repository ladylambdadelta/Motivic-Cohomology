import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.SummaryRepresentatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Localization.Projections.Owner

/-!
# Top-root localization representative summaries

This file exposes one-atom representative count summaries for the six calculus
localization isomorphism hom and inverse arrows at the public root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes the descent-channel hom one-atom representative. -/
theorem AnalyticMotivesRoot.descentChannelIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentChannelIso_hom_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the descent-channel inverse one-atom representative. -/
theorem AnalyticMotivesRoot.descentChannelIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentChannel source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentChannelIso_inv_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the descent-refinement hom one-atom representative. -/
theorem AnalyticMotivesRoot.descentRefinementIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentRefinementIso_hom_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the descent-refinement inverse one-atom representative. -/
theorem AnalyticMotivesRoot.descentRefinementIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentRefinement source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentRefinementIso_inv_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the descent-schedule hom one-atom representative. -/
theorem AnalyticMotivesRoot.descentScheduleIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentScheduleIso_hom_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the descent-schedule inverse one-atom representative. -/
theorem AnalyticMotivesRoot.descentScheduleIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.descentSchedule source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.descentScheduleIso_inv_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the interval-Stokes hom one-atom representative. -/
theorem AnalyticMotivesRoot.intervalStokesIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalStokesIso_hom_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the interval-Stokes inverse one-atom representative. -/
theorem AnalyticMotivesRoot.intervalStokesIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalStokes source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalStokesIso_inv_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the interval-Fubini hom one-atom representative. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalFubiniIso_hom_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the interval-Fubini inverse one-atom representative. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.intervalFubini source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.intervalFubiniIso_inv_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the Tate weight-drop hom one-atom representative. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_hom_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputForward
      (TraceLocalizationInput.tateWeightDrop source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.tateWeightDropIso_hom_localizationSummary_atomCount
    source
    target

/-- The analytic-motives root exposes the Tate weight-drop inverse one-atom representative. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_inv_localizationSummary_atomCount
    (source target : QTraceExpression) :
    (TraceLocalizationWord.ofInputInverse
      (TraceLocalizationInput.tateWeightDrop source target)).atomCount =
      0 + 1 :=
  TraceAnalyticMotive.tateWeightDropIso_inv_localizationSummary_atomCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
