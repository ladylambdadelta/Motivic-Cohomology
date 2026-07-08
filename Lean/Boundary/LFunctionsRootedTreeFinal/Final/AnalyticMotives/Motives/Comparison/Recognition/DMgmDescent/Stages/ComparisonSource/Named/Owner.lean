import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmDescent.Stages.ComparisonSource.Owner

/-!
# Named Boundary DMgm descent formulas for comparison-source recognition stages

This file specializes the comparison-source represented Boundary-DMgm descent
projection formula to the seven named concrete rewrite generators.
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

/-- Boundary-DMgm descent projection formula for the comparison-source Stokes
recognition stage. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_stokesComparisonSourceStage_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition) functor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.stokes source target))) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.stokes source target).targetObject)).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.stokes source target).sourceObject)).hom ≫
        functor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.stokes source target)) :=
  TraceAnalyticMotiveRecognition
    .descendInvertingFunctor_rewriteGeneratorComparisonSourceMap_naturality
      (composition := composition)
      functor
      inverts
      (TraceRewriteGenerator.stokes source target)

/-- Boundary-DMgm descent projection formula for the comparison-source residue
recognition stage. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_residueComparisonSourceStage_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition) functor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.residue source target))) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.residue source target).targetObject)).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.residue source target).sourceObject)).hom ≫
        functor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.residue source target)) :=
  TraceAnalyticMotiveRecognition
    .descendInvertingFunctor_rewriteGeneratorComparisonSourceMap_naturality
      (composition := composition)
      functor
      inverts
      (TraceRewriteGenerator.residue source target)

/-- Boundary-DMgm descent projection formula for the comparison-source channel
recognition stage. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_channelComparisonSourceStage_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition) functor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.channel source target))) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.channel source target).targetObject)).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.channel source target).sourceObject)).hom ≫
        functor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.channel source target)) :=
  TraceAnalyticMotiveRecognition
    .descendInvertingFunctor_rewriteGeneratorComparisonSourceMap_naturality
      (composition := composition)
      functor
      inverts
      (TraceRewriteGenerator.channel source target)

/-- Boundary-DMgm descent projection formula for the comparison-source
refinement recognition stage. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_refinementComparisonSourceStage_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition) functor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.refinement source target))) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.refinement source target).targetObject)).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.refinement source target).sourceObject)).hom ≫
        functor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.refinement source target)) :=
  TraceAnalyticMotiveRecognition
    .descendInvertingFunctor_rewriteGeneratorComparisonSourceMap_naturality
      (composition := composition)
      functor
      inverts
      (TraceRewriteGenerator.refinement source target)

/-- Boundary-DMgm descent projection formula for the comparison-source schedule
recognition stage. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_scheduleComparisonSourceStage_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition) functor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.schedule source target))) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.schedule source target).targetObject)).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.schedule source target).sourceObject)).hom ≫
        functor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.schedule source target)) :=
  TraceAnalyticMotiveRecognition
    .descendInvertingFunctor_rewriteGeneratorComparisonSourceMap_naturality
      (composition := composition)
      functor
      inverts
      (TraceRewriteGenerator.schedule source target)

/-- Boundary-DMgm descent projection formula for the comparison-source
weight-drop recognition stage. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_weightDropComparisonSourceStage_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition) functor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.weightDrop source target))) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.weightDrop source target).targetObject)).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.weightDrop source target).sourceObject)).hom ≫
        functor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.weightDrop source target)) :=
  TraceAnalyticMotiveRecognition
    .descendInvertingFunctor_rewriteGeneratorComparisonSourceMap_naturality
      (composition := composition)
      functor
      inverts
      (TraceRewriteGenerator.weightDrop source target)

/-- Boundary-DMgm descent projection formula for the comparison-source Fubini
recognition stage. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_fubiniComparisonSourceStage_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition) functor inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.fubini source target))) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.fubini source target).targetObject)).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition) functor inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          (TraceRewriteGenerator.fubini source target).sourceObject)).hom ≫
        functor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            (TraceRewriteGenerator.fubini source target)) :=
  TraceAnalyticMotiveRecognition
    .descendInvertingFunctor_rewriteGeneratorComparisonSourceMap_naturality
      (composition := composition)
      functor
      inverts
      (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
