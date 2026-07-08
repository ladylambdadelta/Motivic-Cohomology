import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Naturality.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Naturality.Generators.Named.ConeMap.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Naturality.Generators.Named.ConnectingMap.Owner

/-!
# Named generator naturality for Boundary DMgm descent

This file specializes descended-natural-transformation naturality to the first
maps of the six named stable analytic acyclic generator families and re-exports
the matching cone-map and connecting-map named naturality layers.
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

/-- Naturality on descent-channel stable acyclic generator first maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_descentChannel_generator_firstMap_naturality
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
          (TraceAnalyticStableAcyclicGenerator.descentChannel source target).source) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentChannel source target).firstMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentChannel source target).firstMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.descentChannel source target).target) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_firstMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.descentChannel source target)

/-- Naturality on descent-refinement stable acyclic generator first maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_descentRefinement_generator_firstMap_naturality
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
          (TraceAnalyticStableAcyclicGenerator.descentRefinement source target).source) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentRefinement source target).firstMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentRefinement source target).firstMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.descentRefinement source target).target) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_firstMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.descentRefinement source target)

/-- Naturality on descent-schedule stable acyclic generator first maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_descentSchedule_generator_firstMap_naturality
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
          (TraceAnalyticStableAcyclicGenerator.descentSchedule source target).source) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentSchedule source target).firstMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.descentSchedule source target).firstMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.descentSchedule source target).target) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_firstMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.descentSchedule source target)

/-- Naturality on interval-Stokes stable acyclic generator first maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_intervalStokes_generator_firstMap_naturality
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
          (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).source) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).firstMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).firstMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).target) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_firstMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.intervalStokes source target)

/-- Naturality on interval-Fubini stable acyclic generator first maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_intervalFubini_generator_firstMap_naturality
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
          (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).source) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).firstMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).firstMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).target) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_firstMap_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticStableAcyclicGenerator.intervalFubini source target)

/-- Naturality on Tate-weight-drop stable acyclic generator first maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_tateWeightDrop_generator_firstMap_naturality
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
          (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).source) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).firstMap) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).firstMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).target) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_generator_firstMap_naturality
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
