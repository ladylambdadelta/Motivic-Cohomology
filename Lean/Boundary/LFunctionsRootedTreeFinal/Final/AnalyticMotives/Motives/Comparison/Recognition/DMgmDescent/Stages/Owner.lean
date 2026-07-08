import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.Generators.Stages.Owner

/-!
# Boundary DMgm descent on recognition stages

This file records the target-side projection formula for a null-inverting
homotopy-level functor on the concrete staged rewrite-generator maps.
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

/-- Boundary-DMgm descent projection formula for the homotopy stage of a
concrete rewrite generator. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_rewriteGeneratorHomotopyMap_naturality
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
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap generator)

/-- Boundary-DMgm descent projection formula for the stable stage of a concrete
rewrite generator, expressed through the staged stable map formula. -/
theorem TraceAnalyticMotiveRecognition.descendInvertingFunctor_rewriteGeneratorStableMap_naturality
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
        (TraceAnalyticStableMotiveCategory.mapOf
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap generator)

end AnalyticMotives
end LFunctions
end Boundary
