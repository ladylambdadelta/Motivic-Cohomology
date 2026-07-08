import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.WeightTriangular.Complete.Owner

/-!
# Projections from complete bounded recognition packages

This file exposes named projections from the complete bounded and shifted
bounded weight-triangular recognition packages.
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

/-- Source object data projected from the complete bounded package. -/
theorem TraceAnalyticMotiveRecognition.completeWeightTriangularBoundedMap_sourceObjectData
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularBoundedMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).1.1 =
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_boundedObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      source :=
  rfl

/-- Target object data projected from the complete bounded package. -/
theorem TraceAnalyticMotiveRecognition.completeWeightTriangularBoundedMap_targetObjectData
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularBoundedMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).1.2 =
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_boundedObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      target :=
  rfl

/-- Naturality proof projected from the complete bounded package. -/
theorem TraceAnalyticMotiveRecognition.completeWeightTriangularBoundedMap_naturality
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularBoundedMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).2 =
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_boundedMap_weightTriangular
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom :=
  rfl

/-- Source object data projected from the complete shifted bounded package. -/
theorem TraceAnalyticMotiveRecognition.completeWeightTriangularShiftedBoundedMap_sourceObjectData
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularShiftedBoundedMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom
      degree).1.1 =
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_shiftedBoundedObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      source
      degree :=
  rfl

/-- Target object data projected from the complete shifted bounded package. -/
theorem TraceAnalyticMotiveRecognition.completeWeightTriangularShiftedBoundedMap_targetObjectData
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularShiftedBoundedMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom
      degree).1.2 =
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_shiftedBoundedObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      target
      degree :=
  rfl

/-- Naturality proof projected from the complete shifted bounded package. -/
theorem TraceAnalyticMotiveRecognition.completeWeightTriangularShiftedBoundedMap_naturality
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularShiftedBoundedMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom
      degree).2 =
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_shiftedBoundedMap_weightTriangular
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom
      degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
