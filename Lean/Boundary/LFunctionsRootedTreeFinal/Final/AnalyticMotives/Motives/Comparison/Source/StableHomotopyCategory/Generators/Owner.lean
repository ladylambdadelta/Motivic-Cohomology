import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableHomotopyCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.UniversalProperty.Generators.Owner

/-!
# Generator inversion in the stable homotopy comparison source

This file exposes stable analytic generator-inversion facts through the stable
homotopy comparison source.  The theorems here are routed consequences of the
existing analytic Verdier quotient generator inversion and universal-property
facts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable homotopy comparison quotient functor inverts the first map of
every stable acyclic generator. -/
theorem TraceAnalyticStableHomotopyComparisonSource.generator_firstMap_isIso
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        generator.firstMap) :=
  TraceAnalyticDMgmComparisonSource.generator_firstMap_isIso
    generator

/-- The stable homotopy comparison quotient functor inverts every analytic
localization-input stable map. -/
theorem TraceAnalyticStableHomotopyComparisonSource.localizationInput_stableMap_isIso
    (input : TraceLocalizationInput) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        input.stableMap) :=
  TraceAnalyticDMgmComparisonSource.localizationInput_stableMap_isIso
    input

/-- The stable homotopy comparison quotient functor inverts descent-channel
stable maps. -/
theorem TraceAnalyticStableHomotopyComparisonSource.descentChannel_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentChannel source target).stableMap) :=
  TraceAnalyticDMgmComparisonSource.descentChannel_stableMap_isIso
    source
    target

/-- The stable homotopy comparison quotient functor inverts descent-refinement
stable maps. -/
theorem TraceAnalyticStableHomotopyComparisonSource.descentRefinement_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentRefinement source target).stableMap) :=
  TraceAnalyticDMgmComparisonSource.descentRefinement_stableMap_isIso
    source
    target

/-- The stable homotopy comparison quotient functor inverts descent-schedule
stable maps. -/
theorem TraceAnalyticStableHomotopyComparisonSource.descentSchedule_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentSchedule source target).stableMap) :=
  TraceAnalyticDMgmComparisonSource.descentSchedule_stableMap_isIso
    source
    target

/-- The stable homotopy comparison quotient functor inverts interval-Stokes
stable maps. -/
theorem TraceAnalyticStableHomotopyComparisonSource.intervalStokes_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.intervalStokes source target).stableMap) :=
  TraceAnalyticDMgmComparisonSource.intervalStokes_stableMap_isIso
    source
    target

/-- The stable homotopy comparison quotient functor inverts interval-Fubini
stable maps. -/
theorem TraceAnalyticStableHomotopyComparisonSource.intervalFubini_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.intervalFubini source target).stableMap) :=
  TraceAnalyticDMgmComparisonSource.intervalFubini_stableMap_isIso
    source
    target

/-- The stable homotopy comparison quotient functor inverts Tate-weight-drop
stable maps. -/
theorem TraceAnalyticStableHomotopyComparisonSource.tateWeightDrop_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.tateWeightDrop source target).stableMap) :=
  TraceAnalyticDMgmComparisonSource.tateWeightDrop_stableMap_isIso
    source
    target

/-- A stable homotopy comparison null-inverting functor sends each stable
acyclic generator first map to an isomorphism. -/
theorem TraceAnalyticStableHomotopyComparisonSource.functor_inverts_generator_firstMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso (functor.map generator.firstMap) :=
  TraceAnalyticDMgmComparisonSource.functor_inverts_generator_firstMap
    functor
    inverts
    generator

/-- A stable homotopy comparison null-inverting functor sends each
localization-input stable map to an isomorphism. -/
theorem TraceAnalyticStableHomotopyComparisonSource.functor_inverts_localizationInput_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (input : TraceLocalizationInput) :
    IsIso (functor.map input.stableMap) :=
  TraceAnalyticDMgmComparisonSource.functor_inverts_localizationInput_stableMap
    functor
    inverts
    input

/-- A stable homotopy comparison null-inverting functor sends descent-channel
stable maps to isomorphisms. -/
theorem TraceAnalyticStableHomotopyComparisonSource.functor_inverts_descentChannel_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.descentChannel
          source
          targetExpression).stableMap) :=
  TraceAnalyticDMgmComparisonSource.functor_inverts_descentChannel_stableMap
    functor
    inverts
    source
    targetExpression

/-- A stable homotopy comparison null-inverting functor sends
descent-refinement stable maps to isomorphisms. -/
theorem TraceAnalyticStableHomotopyComparisonSource.functor_inverts_descentRefinement_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.descentRefinement
          source
          targetExpression).stableMap) :=
  TraceAnalyticDMgmComparisonSource.functor_inverts_descentRefinement_stableMap
    functor
    inverts
    source
    targetExpression

/-- A stable homotopy comparison null-inverting functor sends descent-schedule
stable maps to isomorphisms. -/
theorem TraceAnalyticStableHomotopyComparisonSource.functor_inverts_descentSchedule_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.descentSchedule
          source
          targetExpression).stableMap) :=
  TraceAnalyticDMgmComparisonSource.functor_inverts_descentSchedule_stableMap
    functor
    inverts
    source
    targetExpression

/-- A stable homotopy comparison null-inverting functor sends interval-Stokes
stable maps to isomorphisms. -/
theorem TraceAnalyticStableHomotopyComparisonSource.functor_inverts_intervalStokes_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.intervalStokes
          source
          targetExpression).stableMap) :=
  TraceAnalyticDMgmComparisonSource.functor_inverts_intervalStokes_stableMap
    functor
    inverts
    source
    targetExpression

/-- A stable homotopy comparison null-inverting functor sends interval-Fubini
stable maps to isomorphisms. -/
theorem TraceAnalyticStableHomotopyComparisonSource.functor_inverts_intervalFubini_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.intervalFubini
          source
          targetExpression).stableMap) :=
  TraceAnalyticDMgmComparisonSource.functor_inverts_intervalFubini_stableMap
    functor
    inverts
    source
    targetExpression

/-- A stable homotopy comparison null-inverting functor sends Tate-weight-drop
stable maps to isomorphisms. -/
theorem TraceAnalyticStableHomotopyComparisonSource.functor_inverts_tateWeightDrop_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.tateWeightDrop
          source
          targetExpression).stableMap) :=
  TraceAnalyticDMgmComparisonSource.functor_inverts_tateWeightDrop_stableMap
    functor
    inverts
    source
    targetExpression

end AnalyticMotives
end LFunctions
end Boundary
