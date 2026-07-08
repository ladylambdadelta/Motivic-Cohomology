import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.ShortComplex.Owner

/-!
# Motive-root named analytic-generator short complexes

This file exposes the bounded cone short complex and zero-composite fact for
the six concrete analytic localization generators through the motive-root
summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root summary: the descent-channel bounded cone short complex. -/
def TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceLocalizationInput.descentChannel source target).boundedMappingConeShortComplex

/-- Motive-root summary: the descent-channel bounded cone short complex has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeShortComplex_zero
    (TraceLocalizationInput.descentChannel source target)

/-- Motive-root summary: the descent-refinement bounded cone short complex. -/
def TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceLocalizationInput.descentRefinement source target).boundedMappingConeShortComplex

/-- Motive-root summary: the descent-refinement bounded cone short complex has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeShortComplex_zero
    (TraceLocalizationInput.descentRefinement source target)

/-- Motive-root summary: the descent-schedule bounded cone short complex. -/
def TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceLocalizationInput.descentSchedule source target).boundedMappingConeShortComplex

/-- Motive-root summary: the descent-schedule bounded cone short complex has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeShortComplex_zero
    (TraceLocalizationInput.descentSchedule source target)

/-- Motive-root summary: the interval-Stokes bounded cone short complex. -/
def TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceLocalizationInput.intervalStokes source target).boundedMappingConeShortComplex

/-- Motive-root summary: the interval-Stokes bounded cone short complex has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeShortComplex_zero
    (TraceLocalizationInput.intervalStokes source target)

/-- Motive-root summary: the interval-Fubini bounded cone short complex. -/
def TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceLocalizationInput.intervalFubini source target).boundedMappingConeShortComplex

/-- Motive-root summary: the interval-Fubini bounded cone short complex has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeShortComplex_zero
    (TraceLocalizationInput.intervalFubini source target)

/-- Motive-root summary: the Tate-weight-drop bounded cone short complex. -/
def TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex

/-- Motive-root summary: the Tate-weight-drop bounded cone short complex has zero composite. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeShortComplex_zero
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
