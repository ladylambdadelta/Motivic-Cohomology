import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.WeightTriangular.Owner

/-!
# Projections from bounded weight-triangular recognition facts

This file exposes named projections from the bundled bounded and shifted
bounded fully faithful weight-triangular recognition theorems.
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

/-- Fully faithfulness projected from the bounded weight-triangular recognition
theorem. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_boundedMap_fullyFaithful
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).FullyFaithful :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_boundedMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom).1

/-- Bounded-map naturality projected from the bounded weight-triangular
recognition theorem. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_boundedMap_weightTriangular
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful)
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
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_boundedMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom).2

/-- Fully faithfulness projected from the shifted bounded weight-triangular
recognition theorem. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_shiftedBoundedMap_fullyFaithful
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).FullyFaithful :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_shiftedBoundedMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom
    degree).1

/-- Shifted bounded-map naturality projected from the shifted bounded
weight-triangular recognition theorem. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_shiftedBoundedMap_weightTriangular
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
          hom
          degree) ≫
      (TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        target
        degree).hom =
      (TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        source
        degree).hom ≫
        (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).map
          (homotopyFunctor.map
            (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
              hom
              degree)) :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_shiftedBoundedMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom
    degree).2

end AnalyticMotives
end LFunctions
end Boundary
