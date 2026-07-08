import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightRestriction.Bounded.Owner

/-!
# Bounded weight-triangular surface for full recognition functors

This file records the bounded-representative part of the weight-triangular
comparison surface for full recognition functors induced from geometric
recognition data.
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

/-- The full-from-geometric recognition functor sends a stable bounded
analytic representative to the corresponding full Boundary-DMgm image of its
bounded homotopy representative. -/
def TraceAnalyticMotiveRecognition.weightTriangularBoundedObjectIso
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
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricBoundedObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    complex

/-- The bounded weight-triangular object isomorphism is the existing bounded
descent comparison isomorphism. -/
theorem TraceAnalyticMotiveRecognition.weightTriangularBoundedObjectIso_eq
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
    TraceAnalyticMotiveRecognition.weightTriangularBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        complex =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        complex :=
  rfl

/-- Bounded maps satisfy the weight-triangular naturality square for the
full-from-geometric recognition functor. -/
theorem TraceAnalyticMotiveRecognition.weightTriangular_boundedMap_naturality
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
      (TraceAnalyticMotiveRecognition.weightTriangularBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        target).hom =
      (TraceAnalyticMotiveRecognition.weightTriangularBoundedObjectIso
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
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_boundedMap_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom

end AnalyticMotives
end LFunctions
end Boundary
