import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmDescent.Stages.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.Generators.Stages.ComparisonSource.Owner

/-!
# Boundary DMgm descent on comparison-source recognition stages

This file restates the target-side projection formula for a concrete rewrite
generator using the comparison-source represented stable map, rather than the
underlying stable Verdier-quotient name.
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

/-- Boundary-DMgm descent projection formula for the stable stage of a concrete
rewrite generator, expressed through the comparison-source represented map. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_rewriteGeneratorComparisonSourceMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            generator)) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.targetObject)).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.sourceObject)).hom ≫
        functor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            generator) :=
  TraceAnalyticMotiveRecognition
    .descendInvertingFunctor_rewriteGeneratorStableMap_naturality
      (composition := composition)
      functor
      inverts
      generator

end AnalyticMotives
end LFunctions
end Boundary
