import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableHomotopyCategory.Generators.Owner

/-!
# Generator inversion for geometric Boundary DMgm descent

This file specializes the analytic Verdier universal property's generator
inversion consequences to functors landing in the geometric Boundary DMgm
target.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

variable (twistData :
  TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
    (composition := composition))

/-- A geometric Boundary-DMgm comparison functor that inverts stable null
morphisms sends each stable acyclic generator first map to an isomorphism. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_generator_firstMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso (functor.map generator.firstMap) :=
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_generator_firstMap
    functor
    inverts
    generator

/-- A geometric Boundary-DMgm comparison functor that inverts stable null
morphisms sends each localization-input stable map to an isomorphism. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_localizationInput_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (input : TraceLocalizationInput) :
    IsIso (functor.map input.stableMap) :=
  TraceAnalyticStableHomotopyComparisonSource.functor_inverts_localizationInput_stableMap
    functor
    inverts
    input

/-- Geometric Boundary-DMgm comparison functors invert descent-channel stable
maps once they invert stable null morphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_descentChannel_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.descentChannel source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_localizationInput_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.descentChannel source target)

/-- Geometric Boundary-DMgm comparison functors invert descent-refinement
stable maps once they invert stable null morphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_descentRefinement_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.descentRefinement source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_localizationInput_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.descentRefinement source target)

/-- Geometric Boundary-DMgm comparison functors invert descent-schedule stable
maps once they invert stable null morphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_descentSchedule_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.descentSchedule source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_localizationInput_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.descentSchedule source target)

/-- Geometric Boundary-DMgm comparison functors invert interval-Stokes stable
maps once they invert stable null morphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_intervalStokes_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.intervalStokes source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_localizationInput_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.intervalStokes source target)

/-- Geometric Boundary-DMgm comparison functors invert interval-Fubini stable
maps once they invert stable null morphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_intervalFubini_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.intervalFubini source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_localizationInput_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.intervalFubini source target)

/-- Geometric Boundary-DMgm comparison functors invert Tate-weight-drop stable
maps once they invert stable null morphisms. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_tateWeightDrop_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.tateWeightDrop source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_localizationInput_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
