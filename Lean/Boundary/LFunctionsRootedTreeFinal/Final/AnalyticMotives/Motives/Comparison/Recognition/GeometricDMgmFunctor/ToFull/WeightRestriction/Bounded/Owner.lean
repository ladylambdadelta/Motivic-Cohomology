import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.Owner

/-!
# Bounded-weight restriction of full recognition functors from geometric data

This file specializes the full Boundary-DMgm recognition functor induced from
geometric recognition data to stable analytic objects and maps represented by
bounded additive complexes.
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

/-- Object comparison isomorphism for the full-from-geometric recognition
functor on a stable object represented by a bounded analytic complex. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricBoundedObjectIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).obj
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) ≅
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        (homotopyFunctor.obj
          (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
            complex)) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
    (composition := composition)
    (homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      homotopyFunctor
      inverts)
    complex

/-- The bounded object comparison isomorphism is the Boundary-DMgm bounded
descent projection for the postcomposed geometric-to-full homotopy functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricBoundedObjectIso_eq_descended
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        complex =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData)
        (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
          (composition := composition)
          twistData
          homotopyFunctor
          inverts)
        complex :=
  rfl

/-- Naturality of the full-from-geometric recognition functor on a stable map
represented by a bounded analytic chain map. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_boundedMap_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        target).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        source).hom ≫
        (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).map
          (homotopyFunctor.map
            (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap
              hom)) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_boundedMap_naturality
    (composition := composition)
    (homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      homotopyFunctor
      inverts)
    hom

end AnalyticMotives
end LFunctions
end Boundary
