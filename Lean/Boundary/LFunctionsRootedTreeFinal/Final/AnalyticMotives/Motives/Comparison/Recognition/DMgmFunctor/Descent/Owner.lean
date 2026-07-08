import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmDescent.Summary.Owner

/-!
# Recognition functors obtained by Boundary-DMgm descent

This file names the stable recognition functor produced by the existing
Boundary-DMgm descent theorem from a null-inverting homotopy-level functor, and
records its formula on the staged rewrite-generator maps.
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

/-- The stable recognition functor produced from a null-inverting
homotopy-level functor into the Boundary comparison target. -/
def TraceAnalyticMotiveRecognition.descendedDMgmFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticDMgmComparisonSource ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
    (composition := composition)
    homotopyFunctor
    inverts

/-- The stable recognition functor is the Boundary-DMgm descent of the supplied
homotopy-level functor. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_eq_descent
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.descendedDMgmFunctor
        (composition := composition)
        homotopyFunctor
        inverts =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
        (composition := composition)
        homotopyFunctor
        inverts :=
  rfl

/-- Object comparison isomorphism for the descended recognition functor on a
homotopy-stage object. -/
def TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition)
      homotopyFunctor
      inverts).obj
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) ≅
      homotopyFunctor.obj object :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
    (composition := composition)
    homotopyFunctor
    inverts
    object

/-- The object comparison isomorphism for the descended recognition functor is
the Boundary-DMgm descent factorization component. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso_eq_descent
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition)
        homotopyFunctor
        inverts
        object =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        homotopyFunctor
        inverts
        object :=
  rfl

/-- Projection formula for the descended recognition functor on a staged
rewrite-generator map. -/
theorem TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorStage_naturality
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
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
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
  TraceAnalyticMotiveRecognition.descendInvertingFunctor_rewriteGeneratorHomotopyMap_naturality
    (composition := composition)
    homotopyFunctor
    inverts
    generator

end AnalyticMotives
end LFunctions
end Boundary
