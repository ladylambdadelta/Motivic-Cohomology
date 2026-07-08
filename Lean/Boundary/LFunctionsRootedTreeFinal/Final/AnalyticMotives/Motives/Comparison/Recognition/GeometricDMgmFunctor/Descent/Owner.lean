import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.Generators.Stages.Owner

/-!
# Recognition functors obtained by geometric Boundary-DMgm descent

This file gives recognition-facing names to the existing geometric Boundary
DMgm descent construction.  The target is the geometric Tate-stabilized
Boundary motive category, not a fresh comparison target.
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

/-- The stable geometric recognition functor produced from a null-inverting
homotopy-level functor into the geometric Boundary target. -/
def TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticDMgmComparisonSource ⥤
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
    (composition := composition)
    twistData
    homotopyFunctor
    inverts

/-- The stable geometric recognition functor is the existing geometric
Boundary-DMgm descent of the supplied homotopy-level functor. -/
theorem TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor_eq_descent
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts =
      TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts :=
  rfl

/-- Object comparison isomorphism for the descended geometric recognition
functor on a homotopy-stage object. -/
def TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctorObjectIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).obj
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) ≅
      homotopyFunctor.obj object :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    object

/-- Projection formula for the descended geometric recognition functor on a
staged rewrite-generator map. -/
theorem TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor_rewriteGeneratorStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            generator)) ≫
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctorObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctorObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.sourceObject)).hom ≫
        homotopyFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            generator) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap generator)

end AnalyticMotives
end LFunctions
end Boundary
