import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Generators.Owner

/-!
# Endpoint generator inversion for the Boundary DMgm comparison

This file records the comparison-facing consequence of the analytic stable
Verdier quotient: any additive analytic homotopy functor into the concrete or
geometric Boundary DMgm target that descends through the stable quotient
inverts the analytic acyclic generators and the named localization inputs.
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

/-- Endpoint form of stable acyclic-generator inversion in the concrete
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_functor_inverts_generator_firstMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso (functor.map generator.firstMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_generator_firstMap
    (composition := composition)
    functor
    inverts
    generator

/-- Endpoint form of localization-input inversion in the concrete Boundary
DMgm target. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_functor_inverts_localizationInput_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (input : TraceLocalizationInput) :
    IsIso (functor.map input.stableMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_localizationInput_stableMap
    (composition := composition)
    functor
    inverts
    input

/-- Endpoint form of descent-channel stable-map inversion in the concrete
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_functor_inverts_descentChannel_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.descentChannel source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_descentChannel_stableMap
    (composition := composition)
    functor
    inverts
    source
    target

/-- Endpoint form of descent-refinement stable-map inversion in the concrete
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_functor_inverts_descentRefinement_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.descentRefinement source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_descentRefinement_stableMap
    (composition := composition)
    functor
    inverts
    source
    target

/-- Endpoint form of descent-schedule stable-map inversion in the concrete
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_functor_inverts_descentSchedule_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.descentSchedule source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_descentSchedule_stableMap
    (composition := composition)
    functor
    inverts
    source
    target

/-- Endpoint form of interval-Stokes stable-map inversion in the concrete
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_functor_inverts_intervalStokes_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.intervalStokes source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_intervalStokes_stableMap
    (composition := composition)
    functor
    inverts
    source
    target

/-- Endpoint form of interval-Fubini stable-map inversion in the concrete
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_functor_inverts_intervalFubini_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.intervalFubini source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_intervalFubini_stableMap
    (composition := composition)
    functor
    inverts
    source
    target

/-- Endpoint form of Tate-weight-drop stable-map inversion in the concrete
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_functor_inverts_tateWeightDrop_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    IsIso (functor.map
      (TraceLocalizationInput.tateWeightDrop source target).stableMap) :=
  TraceAnalyticDMgmComparisonTarget.functor_inverts_tateWeightDrop_stableMap
    (composition := composition)
    functor
    inverts
    source
    target

variable (twistData :
  TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
    (composition := composition))

/-- Endpoint form of stable acyclic-generator inversion in the geometric
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_functor_inverts_generator_firstMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceAnalyticStableAcyclicGenerator) :
    IsIso (functor.map generator.firstMap) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_generator_firstMap
    (composition := composition)
    twistData
    functor
    inverts
    generator

/-- Endpoint form of localization-input inversion in the geometric Boundary
DMgm target. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_functor_inverts_localizationInput_stableMap
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (input : TraceLocalizationInput) :
    IsIso (functor.map input.stableMap) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_localizationInput_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    input

/-- Endpoint form of descent-channel stable-map inversion in the geometric
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_functor_inverts_descentChannel_stableMap
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
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_descentChannel_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    source
    target

/-- Endpoint form of descent-refinement stable-map inversion in the geometric
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_functor_inverts_descentRefinement_stableMap
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
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_descentRefinement_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    source
    target

/-- Endpoint form of descent-schedule stable-map inversion in the geometric
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_functor_inverts_descentSchedule_stableMap
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
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_descentSchedule_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    source
    target

/-- Endpoint form of interval-Stokes stable-map inversion in the geometric
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_functor_inverts_intervalStokes_stableMap
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
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_intervalStokes_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    source
    target

/-- Endpoint form of interval-Fubini stable-map inversion in the geometric
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_functor_inverts_intervalFubini_stableMap
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
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_intervalFubini_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    source
    target

/-- Endpoint form of Tate-weight-drop stable-map inversion in the geometric
Boundary DMgm target. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_functor_inverts_tateWeightDrop_stableMap
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
  TraceAnalyticDMgmComparisonTarget.Geometric.functor_inverts_tateWeightDrop_stableMap
    (composition := composition)
    twistData
    functor
    inverts
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
