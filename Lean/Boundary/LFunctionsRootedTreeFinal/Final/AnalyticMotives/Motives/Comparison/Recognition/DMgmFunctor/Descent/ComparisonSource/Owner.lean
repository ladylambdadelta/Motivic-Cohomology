import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmDescent.Stages.ComparisonSource.Owner

/-!
# Descended recognition functors on comparison-source stages

This file records the projection formula for the descended recognition functor
on the comparison-source represented stable map of a concrete rewrite
generator.
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

/-- Projection formula for the descended recognition functor on the
comparison-source represented stable map of a concrete rewrite generator. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorComparisonSourceStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition)
      homotopyFunctor
      inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            generator)) ≫
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition)
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition)
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.sourceObject)).hom ≫
        homotopyFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            generator) :=
  TraceAnalyticMotiveRecognition
    .descendInvertingFunctor_rewriteGeneratorComparisonSourceMap_naturality
      (composition := composition)
      homotopyFunctor
      inverts
      generator

end AnalyticMotives
end LFunctions
end Boundary
