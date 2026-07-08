import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.Owner

/-!
# Named formulas for full recognition functors induced from geometric data

This file specializes the full Boundary-DMgm recognition functor induced from
geometric recognition data to the seven named concrete rewrite generators.
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

/-- Full recognition-from-geometric projection formula for Stokes. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_stokesStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.stokes source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.stokes source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.stokes source target).sourceObject)).hom ≫
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.stokes source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_rewriteGeneratorStage_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.stokes source target)

/-- Full recognition-from-geometric projection formula for residue. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_residueStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.residue source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.residue source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.residue source target).sourceObject)).hom ≫
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.residue source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_rewriteGeneratorStage_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.residue source target)

/-- Full recognition-from-geometric projection formula for channel. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_channelStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.channel source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.channel source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.channel source target).sourceObject)).hom ≫
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.channel source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_rewriteGeneratorStage_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.channel source target)

/-- Full recognition-from-geometric projection formula for refinement. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_refinementStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.refinement source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.refinement source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.refinement source target).sourceObject)).hom ≫
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.refinement source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_rewriteGeneratorStage_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.refinement source target)

/-- Full recognition-from-geometric projection formula for schedule. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_scheduleStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.schedule source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.schedule source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.schedule source target).sourceObject)).hom ≫
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.schedule source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_rewriteGeneratorStage_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.schedule source target)

/-- Full recognition-from-geometric projection formula for weight-drop. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_weightDropStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.weightDrop source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.weightDrop source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.weightDrop source target).sourceObject)).hom ≫
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.weightDrop source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_rewriteGeneratorStage_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.weightDrop source target)

/-- Full recognition-from-geometric projection formula for Fubini. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fubiniStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.fubini source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.fubini source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.fubini source target).sourceObject)).hom ≫
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.fubini source target)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_rewriteGeneratorStage_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
