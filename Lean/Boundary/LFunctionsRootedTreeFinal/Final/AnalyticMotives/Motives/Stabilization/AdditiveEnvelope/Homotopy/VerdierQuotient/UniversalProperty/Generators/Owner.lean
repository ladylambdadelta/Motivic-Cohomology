import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.UniversalProperty.Owner

/-!
# Generator consequences of the analytic Verdier universal property

Any functor out of the additive analytic homotopy category that inverts the
stable null morphisms sends the concrete analytic localization maps to
isomorphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A null-inverting functor sends each stable acyclic generator first map to an isomorphism. -/
theorem TraceAnalyticStableMotiveCategory.functor_inverts_generator_firstMap
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso (functor.map generator.firstMap) :=
  inverts
    generator.firstMap
    (TraceAnalyticStableNullSubcategory.generator_firstMap_inverted generator)

/-- A null-inverting functor sends each analytic localization-input stable map to an isomorphism. -/
theorem TraceAnalyticStableMotiveCategory.functor_inverts_localizationInput_stableMap
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor)
    (input : TraceLocalizationInput) :
    IsIso (functor.map input.stableMap) :=
  Eq.subst
    (motive :=
      fun hom =>
        IsIso (functor.map hom))
    (TraceAnalyticStableAcyclicGenerator.firstMap_eq_input_stableMap
      ({ input := input } : TraceAnalyticStableAcyclicGenerator))
    (TraceAnalyticStableMotiveCategory.functor_inverts_generator_firstMap
      functor
      inverts
      ({ input := input } : TraceAnalyticStableAcyclicGenerator))

/-- A null-inverting functor sends descent-channel stable maps to isomorphisms. -/
theorem TraceAnalyticStableMotiveCategory.functor_inverts_descentChannel_stableMap
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso (functor.map (TraceLocalizationInput.descentChannel source targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_localizationInput_stableMap
    functor
    inverts
    (TraceLocalizationInput.descentChannel source targetExpression)

/-- A null-inverting functor sends descent-refinement stable maps to isomorphisms. -/
theorem TraceAnalyticStableMotiveCategory.functor_inverts_descentRefinement_stableMap
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso (functor.map (TraceLocalizationInput.descentRefinement source targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_localizationInput_stableMap
    functor
    inverts
    (TraceLocalizationInput.descentRefinement source targetExpression)

/-- A null-inverting functor sends descent-schedule stable maps to isomorphisms. -/
theorem TraceAnalyticStableMotiveCategory.functor_inverts_descentSchedule_stableMap
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso (functor.map (TraceLocalizationInput.descentSchedule source targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_localizationInput_stableMap
    functor
    inverts
    (TraceLocalizationInput.descentSchedule source targetExpression)

/-- A null-inverting functor sends interval-Stokes stable maps to isomorphisms. -/
theorem TraceAnalyticStableMotiveCategory.functor_inverts_intervalStokes_stableMap
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso (functor.map (TraceLocalizationInput.intervalStokes source targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_localizationInput_stableMap
    functor
    inverts
    (TraceLocalizationInput.intervalStokes source targetExpression)

/-- A null-inverting functor sends interval-Fubini stable maps to isomorphisms. -/
theorem TraceAnalyticStableMotiveCategory.functor_inverts_intervalFubini_stableMap
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso (functor.map (TraceLocalizationInput.intervalFubini source targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_localizationInput_stableMap
    functor
    inverts
    (TraceLocalizationInput.intervalFubini source targetExpression)

/-- A null-inverting functor sends Tate-weight-drop stable maps to isomorphisms. -/
theorem TraceAnalyticStableMotiveCategory.functor_inverts_tateWeightDrop_stableMap
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor)
    (source targetExpression : QTraceExpression) :
    IsIso (functor.map (TraceLocalizationInput.tateWeightDrop source targetExpression).stableMap) :=
  TraceAnalyticStableMotiveCategory.functor_inverts_localizationInput_stableMap
    functor
    inverts
    (TraceLocalizationInput.tateWeightDrop source targetExpression)

end AnalyticMotives
end LFunctions
end Boundary
