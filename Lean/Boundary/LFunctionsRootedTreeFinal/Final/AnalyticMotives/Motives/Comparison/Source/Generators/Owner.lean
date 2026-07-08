import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Owner

/-!
# Generator inversion in the analytic comparison source

This file exposes the stable analytic Verdier quotient's generator inversion
facts under comparison-source names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The comparison-source quotient functor inverts the first map of every
stable acyclic generator. -/
theorem TraceAnalyticDMgmComparisonSource.generator_firstMap_isIso
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        generator.firstMap) :=
  TraceAnalyticStableMotiveCategory.generator_firstMap_isIso
    generator

/-- The comparison-source quotient functor inverts every analytic
localization-input stable map. -/
theorem TraceAnalyticDMgmComparisonSource.localizationInput_stableMap_isIso
    (input : TraceLocalizationInput) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        input.stableMap) :=
  TraceAnalyticStableMotiveCategory.localizationInput_stableMap_isIso
    input

/-- The comparison-source quotient functor inverts descent-channel stable
maps. -/
theorem TraceAnalyticDMgmComparisonSource.descentChannel_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentChannel source target).stableMap) :=
  TraceAnalyticStableMotiveCategory.descentChannel_stableMap_isIso
    source
    target

/-- The comparison-source quotient functor inverts descent-refinement stable
maps. -/
theorem TraceAnalyticDMgmComparisonSource.descentRefinement_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentRefinement source target).stableMap) :=
  TraceAnalyticStableMotiveCategory.descentRefinement_stableMap_isIso
    source
    target

/-- The comparison-source quotient functor inverts descent-schedule stable
maps. -/
theorem TraceAnalyticDMgmComparisonSource.descentSchedule_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentSchedule source target).stableMap) :=
  TraceAnalyticStableMotiveCategory.descentSchedule_stableMap_isIso
    source
    target

/-- The comparison-source quotient functor inverts interval-Stokes stable
maps. -/
theorem TraceAnalyticDMgmComparisonSource.intervalStokes_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.intervalStokes source target).stableMap) :=
  TraceAnalyticStableMotiveCategory.intervalStokes_stableMap_isIso
    source
    target

/-- The comparison-source quotient functor inverts interval-Fubini stable
maps. -/
theorem TraceAnalyticDMgmComparisonSource.intervalFubini_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.intervalFubini source target).stableMap) :=
  TraceAnalyticStableMotiveCategory.intervalFubini_stableMap_isIso
    source
    target

/-- The comparison-source quotient functor inverts Tate-weight-drop stable
maps. -/
theorem TraceAnalyticDMgmComparisonSource.tateWeightDrop_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.tateWeightDrop source target).stableMap) :=
  TraceAnalyticStableMotiveCategory.tateWeightDrop_stableMap_isIso
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
