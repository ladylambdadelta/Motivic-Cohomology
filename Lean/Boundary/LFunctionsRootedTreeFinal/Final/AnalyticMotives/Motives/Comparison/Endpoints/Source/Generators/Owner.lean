import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableHomotopyCategory.Generators.Owner

/-!
# Endpoint source generator inversion

This file exposes the stable analytic comparison source's generator inversion
facts at endpoint names.  These are the source-side localization facts that a
later analytic-to-`DMgm` comparison functor must respect.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Endpoint form: the source quotient functor inverts every stable acyclic
generator first map. -/
theorem TraceAnalyticMotiveComparison.sourceQuotient_generator_firstMap_isIso
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        generator.firstMap) :=
  TraceAnalyticStableHomotopyComparisonSource.generator_firstMap_isIso
    generator

/-- Endpoint form: the source quotient functor inverts every analytic
localization-input stable map. -/
theorem TraceAnalyticMotiveComparison.sourceQuotient_localizationInput_stableMap_isIso
    (input : TraceLocalizationInput) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        input.stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.localizationInput_stableMap_isIso
    input

/-- Endpoint form: the source quotient functor inverts descent-channel stable
maps. -/
theorem TraceAnalyticMotiveComparison.sourceQuotient_descentChannel_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentChannel source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.descentChannel_stableMap_isIso
    source
    target

/-- Endpoint form: the source quotient functor inverts descent-refinement
stable maps. -/
theorem TraceAnalyticMotiveComparison.sourceQuotient_descentRefinement_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentRefinement source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.descentRefinement_stableMap_isIso
    source
    target

/-- Endpoint form: the source quotient functor inverts descent-schedule stable
maps. -/
theorem TraceAnalyticMotiveComparison.sourceQuotient_descentSchedule_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentSchedule source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.descentSchedule_stableMap_isIso
    source
    target

/-- Endpoint form: the source quotient functor inverts interval-Stokes stable
maps. -/
theorem TraceAnalyticMotiveComparison.sourceQuotient_intervalStokes_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.intervalStokes source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.intervalStokes_stableMap_isIso
    source
    target

/-- Endpoint form: the source quotient functor inverts interval-Fubini stable
maps. -/
theorem TraceAnalyticMotiveComparison.sourceQuotient_intervalFubini_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.intervalFubini source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.intervalFubini_stableMap_isIso
    source
    target

/-- Endpoint form: the source quotient functor inverts Tate-weight-drop stable
maps. -/
theorem TraceAnalyticMotiveComparison.sourceQuotient_tateWeightDrop_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.tateWeightDrop source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.tateWeightDrop_stableMap_isIso
    source
    target

/-- Stable-homotopy endpoint form: the stable homotopy comparison quotient
functor inverts every stable acyclic generator first map. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceQuotient_generator_firstMap_isIso
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        generator.firstMap) :=
  TraceAnalyticStableHomotopyComparisonSource.generator_firstMap_isIso
    generator

/-- Stable-homotopy endpoint form: the stable homotopy comparison quotient
functor inverts every analytic localization-input stable map. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceQuotient_localizationInput_stableMap_isIso
    (input : TraceLocalizationInput) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        input.stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.localizationInput_stableMap_isIso
    input

/-- Stable-homotopy endpoint form: the stable homotopy comparison quotient
functor inverts descent-channel stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceQuotient_descentChannel_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentChannel source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.descentChannel_stableMap_isIso
    source
    target

/-- Stable-homotopy endpoint form: the stable homotopy comparison quotient
functor inverts descent-refinement stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceQuotient_descentRefinement_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentRefinement source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.descentRefinement_stableMap_isIso
    source
    target

/-- Stable-homotopy endpoint form: the stable homotopy comparison quotient
functor inverts descent-schedule stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceQuotient_descentSchedule_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.descentSchedule source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.descentSchedule_stableMap_isIso
    source
    target

/-- Stable-homotopy endpoint form: the stable homotopy comparison quotient
functor inverts interval-Stokes stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceQuotient_intervalStokes_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.intervalStokes source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.intervalStokes_stableMap_isIso
    source
    target

/-- Stable-homotopy endpoint form: the stable homotopy comparison quotient
functor inverts interval-Fubini stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceQuotient_intervalFubini_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.intervalFubini source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.intervalFubini_stableMap_isIso
    source
    target

/-- Stable-homotopy endpoint form: the stable homotopy comparison quotient
functor inverts Tate-weight-drop stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceQuotient_tateWeightDrop_stableMap_isIso
    (source target : QTraceExpression) :
    IsIso
      (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.map
        (TraceLocalizationInput.tateWeightDrop source target).stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.tateWeightDrop_stableMap_isIso
    source
    target

/-- Endpoint universal-property form: any comparison-source null-inverting
functor inverts stable acyclic generator first maps. -/
theorem TraceAnalyticMotiveComparison.sourceFunctor_inverts_generator_firstMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso (functor.map generator.firstMap) :=
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_generator_firstMap
    functor
    inverts
    generator

/-- Endpoint universal-property form: any comparison-source null-inverting
functor inverts localization-input stable maps. -/
theorem TraceAnalyticMotiveComparison.sourceFunctor_inverts_localizationInput_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor)
    (input : TraceLocalizationInput) :
    IsIso (functor.map input.stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_localizationInput_stableMap
    functor
    inverts
    input

/-- Endpoint universal-property form: null-inverting functors invert
descent-channel stable maps. -/
theorem TraceAnalyticMotiveComparison.sourceFunctor_inverts_descentChannel_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_descentChannel_stableMap
    functor
    inverts
    source
    targetExpression

/-- Endpoint universal-property form: null-inverting functors invert
descent-refinement stable maps. -/
theorem TraceAnalyticMotiveComparison.sourceFunctor_inverts_descentRefinement_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_descentRefinement_stableMap
    functor
    inverts
    source
    targetExpression

/-- Endpoint universal-property form: null-inverting functors invert
descent-schedule stable maps. -/
theorem TraceAnalyticMotiveComparison.sourceFunctor_inverts_descentSchedule_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_descentSchedule_stableMap
    functor
    inverts
    source
    targetExpression

/-- Endpoint universal-property form: null-inverting functors invert
interval-Stokes stable maps. -/
theorem TraceAnalyticMotiveComparison.sourceFunctor_inverts_intervalStokes_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_intervalStokes_stableMap
    functor
    inverts
    source
    targetExpression

/-- Endpoint universal-property form: null-inverting functors invert
interval-Fubini stable maps. -/
theorem TraceAnalyticMotiveComparison.sourceFunctor_inverts_intervalFubini_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_intervalFubini_stableMap
    functor
    inverts
    source
    targetExpression

/-- Endpoint universal-property form: null-inverting functors invert
Tate-weight-drop stable maps. -/
theorem TraceAnalyticMotiveComparison.sourceFunctor_inverts_tateWeightDrop_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_tateWeightDrop_stableMap
    functor
    inverts
    source
    targetExpression

/-- Stable-homotopy endpoint form: any stable homotopy comparison
null-inverting functor inverts stable acyclic generator first maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceFunctor_inverts_generator_firstMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso (functor.map generator.firstMap) :=
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_generator_firstMap
    functor
    inverts
    generator

/-- Stable-homotopy endpoint form: any stable homotopy comparison
null-inverting functor inverts localization-input stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceFunctor_inverts_localizationInput_stableMap
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (input : TraceLocalizationInput) :
    IsIso (functor.map input.stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_localizationInput_stableMap
    functor
    inverts
    input

/-- Stable-homotopy endpoint form: null-inverting functors invert
descent-channel stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceFunctor_inverts_descentChannel_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_descentChannel_stableMap
    functor
    inverts
    source
    targetExpression

/-- Stable-homotopy endpoint form: null-inverting functors invert
descent-refinement stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceFunctor_inverts_descentRefinement_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_descentRefinement_stableMap
    functor
    inverts
    source
    targetExpression

/-- Stable-homotopy endpoint form: null-inverting functors invert
descent-schedule stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceFunctor_inverts_descentSchedule_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_descentSchedule_stableMap
    functor
    inverts
    source
    targetExpression

/-- Stable-homotopy endpoint form: null-inverting functors invert
interval-Stokes stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceFunctor_inverts_intervalStokes_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_intervalStokes_stableMap
    functor
    inverts
    source
    targetExpression

/-- Stable-homotopy endpoint form: null-inverting functors invert
interval-Fubini stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceFunctor_inverts_intervalFubini_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_intervalFubini_stableMap
    functor
    inverts
    source
    targetExpression

/-- Stable-homotopy endpoint form: null-inverting functors invert
Tate-weight-drop stable maps. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceFunctor_inverts_tateWeightDrop_stableMap
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
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_tateWeightDrop_stableMap
    functor
    inverts
    source
    targetExpression

end AnalyticMotives
end LFunctions
end Boundary
