import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.UniversalProperty.Generators.Owner

/-!
# Universal-property generator consequences for the comparison source

This file exposes the generator-level consequences of the stable analytic
Verdier quotient universal property under comparison-source names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A comparison-source null-inverting functor sends each stable acyclic
generator first map to an isomorphism. -/
theorem TraceAnalyticDMgmComparisonSource.functor_inverts_generator_firstMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso (functor.map generator.firstMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_generator_firstMap
    functor
    inverts
    generator

/-- A comparison-source null-inverting functor sends each localization-input
stable map to an isomorphism. -/
theorem TraceAnalyticDMgmComparisonSource.functor_inverts_localizationInput_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (input : TraceLocalizationInput) :
    IsIso (functor.map input.stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_localizationInput_stableMap
    functor
    inverts
    input

/-- A comparison-source null-inverting functor sends descent-channel stable maps
to isomorphisms. -/
theorem TraceAnalyticDMgmComparisonSource.functor_inverts_descentChannel_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.descentChannel
          source
          targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_descentChannel_stableMap
    functor
    inverts
    source
    targetExpression

/-- A comparison-source null-inverting functor sends descent-refinement stable
maps to isomorphisms. -/
theorem TraceAnalyticDMgmComparisonSource.functor_inverts_descentRefinement_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.descentRefinement
          source
          targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_descentRefinement_stableMap
    functor
    inverts
    source
    targetExpression

/-- A comparison-source null-inverting functor sends descent-schedule stable
maps to isomorphisms. -/
theorem TraceAnalyticDMgmComparisonSource.functor_inverts_descentSchedule_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.descentSchedule
          source
          targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_descentSchedule_stableMap
    functor
    inverts
    source
    targetExpression

/-- A comparison-source null-inverting functor sends interval-Stokes stable maps
to isomorphisms. -/
theorem TraceAnalyticDMgmComparisonSource.functor_inverts_intervalStokes_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.intervalStokes
          source
          targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_intervalStokes_stableMap
    functor
    inverts
    source
    targetExpression

/-- A comparison-source null-inverting functor sends interval-Fubini stable maps
to isomorphisms. -/
theorem TraceAnalyticDMgmComparisonSource.functor_inverts_intervalFubini_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.intervalFubini
          source
          targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_intervalFubini_stableMap
    functor
    inverts
    source
    targetExpression

/-- A comparison-source null-inverting functor sends Tate-weight-drop stable
maps to isomorphisms. -/
theorem TraceAnalyticDMgmComparisonSource.functor_inverts_tateWeightDrop_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso
      (functor.map
        (TraceLocalizationInput.tateWeightDrop
          source
          targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_tateWeightDrop_stableMap
    functor
    inverts
    source
    targetExpression

end AnalyticMotives
end LFunctions
end Boundary
