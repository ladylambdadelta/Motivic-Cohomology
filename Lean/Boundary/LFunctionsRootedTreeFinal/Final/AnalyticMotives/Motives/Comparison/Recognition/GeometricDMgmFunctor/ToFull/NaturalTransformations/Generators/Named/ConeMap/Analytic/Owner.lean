import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Naturality.Generators.Named.ConeMap.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.NaturalTransformations.Generators.Named.ConeMap.Owner

/-!
# Analytic named cone-map naturality

This file specializes interval-Stokes, interval-Fubini, and Tate-weight-drop
stable acyclic generator cone-map naturality to descended natural
transformations between full recognition functors induced from geometric data.
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

/-- Naturality on interval-Stokes stable acyclic generator cone maps. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans_intervalStokes_generator_coneMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation :
      first ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData ⟶
      second ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).target) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).coneMap) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).coneMap) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_intervalStokes_generator_coneMap_naturality
    (composition := composition)
    (first ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (second ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      first
      firstInverts)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      second
      secondInverts)
    transformation
    source
    target

/-- Naturality on interval-Fubini stable acyclic generator cone maps. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans_intervalFubini_generator_coneMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation :
      first ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData ⟶
      second ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).target) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).coneMap) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).coneMap) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_intervalFubini_generator_coneMap_naturality
    (composition := composition)
    (first ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (second ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      first
      firstInverts)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      second
      secondInverts)
    transformation
    source
    target

/-- Naturality on Tate-weight-drop stable acyclic generator cone maps. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans_tateWeightDrop_generator_coneMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation :
      first ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData ⟶
      second ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf
          (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).target) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).coneMap) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf
            (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).coneMap) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf
            (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).object) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_tateWeightDrop_generator_coneMap_naturality
    (composition := composition)
    (first ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (second ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      first
      firstInverts)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      second
      secondInverts)
    transformation
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
