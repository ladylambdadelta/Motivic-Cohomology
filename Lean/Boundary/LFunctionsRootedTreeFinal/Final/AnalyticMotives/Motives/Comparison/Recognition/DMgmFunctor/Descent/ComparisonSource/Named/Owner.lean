import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.Descent.ComparisonSource.Owner

/-!
# Named descended recognition-functor formulas on comparison-source stages

This file specializes the descended recognition-functor projection formula on
comparison-source represented stable maps to the seven named concrete rewrite
generators.
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

/-- Descended recognition-functor projection formula for the comparison-source
Stokes stage. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_stokesComparisonSourceStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
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
  TraceAnalyticMotiveRecognition
    .descendedDMgmFunctor_rewriteGeneratorComparisonSourceStage_naturality
      (composition := composition)
      homotopyFunctor
      inverts
      (TraceRewriteGenerator.stokes source target)

/-- Descended recognition-functor projection formula for the comparison-source
residue stage. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_residueComparisonSourceStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
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
  TraceAnalyticMotiveRecognition
    .descendedDMgmFunctor_rewriteGeneratorComparisonSourceStage_naturality
      (composition := composition)
      homotopyFunctor
      inverts
      (TraceRewriteGenerator.residue source target)

/-- Descended recognition-functor projection formula for the comparison-source
channel stage. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_channelComparisonSourceStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
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
  TraceAnalyticMotiveRecognition
    .descendedDMgmFunctor_rewriteGeneratorComparisonSourceStage_naturality
      (composition := composition)
      homotopyFunctor
      inverts
      (TraceRewriteGenerator.channel source target)

/-- Descended recognition-functor projection formula for the comparison-source
refinement stage. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_refinementComparisonSourceStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
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
  TraceAnalyticMotiveRecognition
    .descendedDMgmFunctor_rewriteGeneratorComparisonSourceStage_naturality
      (composition := composition)
      homotopyFunctor
      inverts
      (TraceRewriteGenerator.refinement source target)

/-- Descended recognition-functor projection formula for the comparison-source
schedule stage. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_scheduleComparisonSourceStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
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
  TraceAnalyticMotiveRecognition
    .descendedDMgmFunctor_rewriteGeneratorComparisonSourceStage_naturality
      (composition := composition)
      homotopyFunctor
      inverts
      (TraceRewriteGenerator.schedule source target)

/-- Descended recognition-functor projection formula for the comparison-source
weight-drop stage. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_weightDropComparisonSourceStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
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
  TraceAnalyticMotiveRecognition
    .descendedDMgmFunctor_rewriteGeneratorComparisonSourceStage_naturality
      (composition := composition)
      homotopyFunctor
      inverts
      (TraceRewriteGenerator.weightDrop source target)

/-- Descended recognition-functor projection formula for the comparison-source
Fubini stage. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_fubiniComparisonSourceStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition) homotopyFunctor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
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
  TraceAnalyticMotiveRecognition
    .descendedDMgmFunctor_rewriteGeneratorComparisonSourceStage_naturality
      (composition := composition)
      homotopyFunctor
      inverts
      (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
