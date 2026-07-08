import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.WeightTriangular.Owner

/-!
# Mapping-cone fully faithful weight-triangular recognition theorem

This file bundles the fully faithful full-recognition theorem with the three
mapping-cone naturality equations that form the bounded weight-triangular
triangle surface.
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

/-- The full-from-geometric recognition functor is fully faithful and sends a
bounded analytic mapping-cone triangle to the corresponding full Boundary-DMgm
mapping-cone triangle, with naturality on the first map, second map, and
connecting map. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeTriangle
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
      (composition := composition) twistData homotopyFunctor inverts).FullyFaithful ∧
    (((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
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
              hom))) ∧
    (((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
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
              hom))) ∧
    ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
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
              hom)))) :=
  And.intro
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful)
    (And.intro
      (TraceAnalyticMotiveRecognition.weightTriangular_mappingConeFirstMap_naturality
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom)
      (And.intro
        (TraceAnalyticMotiveRecognition.weightTriangular_mappingConeSecondMap_naturality
          (composition := composition)
          twistData
          homotopyFunctor
          inverts
          hom)
        (TraceAnalyticMotiveRecognition.weightTriangular_mappingConeConnectingMap_naturality
          (composition := composition)
          twistData
          homotopyFunctor
          inverts
          hom)))

end AnalyticMotives
end LFunctions
end Boundary
