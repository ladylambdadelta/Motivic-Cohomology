import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Naturality.Generators.Owner

/-!
# Named generator cone-map naturality for Boundary DMgm descent

This file specializes descended-natural-transformation naturality to the cone
maps of the six named stable analytic acyclic generator families.
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

/-- Naturality on descent-channel stable acyclic generator cone maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_descentChannel_generator_coneMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceAnalyticStableAcyclicGenerator.descentChannel source target).target) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentChannel source target).coneMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentChannel source target).coneMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.descentChannel source target).object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_coneMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.descentChannel source target)

/-- Naturality on descent-refinement stable acyclic generator cone maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_descentRefinement_generator_coneMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceAnalyticStableAcyclicGenerator.descentRefinement source target).target) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentRefinement source target).coneMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentRefinement source target).coneMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.descentRefinement source target).object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_coneMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.descentRefinement source target)

/-- Naturality on descent-schedule stable acyclic generator cone maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_descentSchedule_generator_coneMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceAnalyticStableAcyclicGenerator.descentSchedule source target).target) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentSchedule source target).coneMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentSchedule source target).coneMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.descentSchedule source target).object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_coneMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.descentSchedule source target)

/-- Naturality on interval-Stokes stable acyclic generator cone maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_intervalStokes_generator_coneMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).target) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).coneMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).coneMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_coneMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.intervalStokes source target)

/-- Naturality on interval-Fubini stable acyclic generator cone maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_intervalFubini_generator_coneMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).target) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).coneMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).coneMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_coneMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.intervalFubini source target)

/-- Naturality on Tate-weight-drop stable acyclic generator cone maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_tateWeightDrop_generator_coneMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).target) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).coneMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).coneMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_coneMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
