import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.Descent.Owner

/-!
# Named formulas for descended recognition functors

This file specializes the descended recognition functor projection formula to
the seven named concrete rewrite generators.
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

/-- Descended recognition-functor projection formula for Stokes. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_stokesStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.stokes source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.stokes source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.stokes source target).sourceObject)).hom ≫
        homotopyFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.stokes source target)) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorStage_naturality
    (composition := composition)
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.stokes source target)

/-- Descended recognition-functor projection formula for residue. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_residueStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.residue source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.residue source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.residue source target).sourceObject)).hom ≫
        homotopyFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.residue source target)) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorStage_naturality
    (composition := composition)
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.residue source target)

/-- Descended recognition-functor projection formula for channel. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_channelStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.channel source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.channel source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.channel source target).sourceObject)).hom ≫
        homotopyFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.channel source target)) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorStage_naturality
    (composition := composition)
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.channel source target)

/-- Descended recognition-functor projection formula for refinement. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_refinementStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.refinement source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.refinement source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.refinement source target).sourceObject)).hom ≫
        homotopyFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.refinement source target)) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorStage_naturality
    (composition := composition)
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.refinement source target)

/-- Descended recognition-functor projection formula for schedule. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_scheduleStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.schedule source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.schedule source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.schedule source target).sourceObject)).hom ≫
        homotopyFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.schedule source target)) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorStage_naturality
    (composition := composition)
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.schedule source target)

/-- Descended recognition-functor projection formula for weight-drop. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_weightDropStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.weightDrop source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.weightDrop source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.weightDrop source target).sourceObject)).hom ≫
        homotopyFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.weightDrop source target)) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorStage_naturality
    (composition := composition)
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.weightDrop source target)

/-- Descended recognition-functor projection formula for Fubini. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_fubiniStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.fubini source target))) ≫
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.fubini source target).targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition) homotopyFunctor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.fubini source target).sourceObject)).hom ≫
        homotopyFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.fubini source target)) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorStage_naturality
    (composition := composition)
    homotopyFunctor
    inverts
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
