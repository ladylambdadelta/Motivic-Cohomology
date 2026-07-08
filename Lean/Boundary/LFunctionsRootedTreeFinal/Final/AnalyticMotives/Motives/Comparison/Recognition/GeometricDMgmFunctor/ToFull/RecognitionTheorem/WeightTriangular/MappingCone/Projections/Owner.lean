import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.WeightTriangular.MappingCone.Owner

/-!
# Projections from the mapping-cone recognition theorem

This file exposes named projections from the bundled fully faithful
weight-triangular mapping-cone recognition theorem.
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

/-- Fully faithfulness projected from the bundled mapping-cone recognition
theorem. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeTriangle_fullyFaithful
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
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeTriangle
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom).1

/-- The first-map naturality square projected from the bundled mapping-cone
recognition theorem. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeTriangle_firstMap
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
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstMap
          hom) ≫
      (TraceAnalyticMotiveRecognition.weightTriangularMappingConeSecondObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom).hom =
      (TraceAnalyticMotiveRecognition.weightTriangularMappingConeFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom).hom ≫
        (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).map
          (homotopyFunctor.map
            (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstMap
              hom)) :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeTriangle
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom).2.1

/-- The second-map naturality square projected from the bundled mapping-cone
recognition theorem. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeTriangle_secondMap
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
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondMap
          hom) ≫
      (TraceAnalyticMotiveRecognition.weightTriangularMappingConeThirdObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom).hom =
      (TraceAnalyticMotiveRecognition.weightTriangularMappingConeSecondObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom).hom ≫
        (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).map
          (homotopyFunctor.map
            (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondMap
              hom)) :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeTriangle
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom).2.2.1

/-- The connecting-map naturality square projected from the bundled
mapping-cone recognition theorem. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeTriangle_connectingMap
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
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableConnectingMap
          hom) ≫
      (TraceAnalyticMotiveRecognition.weightTriangularMappingConeShiftedFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom).hom =
      (TraceAnalyticMotiveRecognition.weightTriangularMappingConeThirdObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom).hom ≫
        (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).map
          (homotopyFunctor.map
            (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.connectingMap
              hom)) :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeTriangle
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom).2.2.2

end AnalyticMotives
end LFunctions
end Boundary
