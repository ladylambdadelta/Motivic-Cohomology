import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightRestriction.MappingCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightTriangular.Bounded.Owner

/-!
# Mapping-cone weight-triangular surface for full recognition functors

This file records the bounded mapping-cone part of the weight-triangular
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

/-- The first vertex of a bounded analytic mapping-cone triangle is transported
by the full-from-geometric recognition functor to the corresponding first
geometric vertex in the full Boundary-DMgm target. -/
def TraceAnalyticMotiveRecognition.weightTriangularMappingConeFirstObjectIso
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
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
          hom) ≅
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        (homotopyFunctor.obj
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
            hom)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeFirstObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom

/-- The second vertex of a bounded analytic mapping-cone triangle is transported
by the full-from-geometric recognition functor to the corresponding second
geometric vertex in the full Boundary-DMgm target. -/
def TraceAnalyticMotiveRecognition.weightTriangularMappingConeSecondObjectIso
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
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
          hom) ≅
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        (homotopyFunctor.obj
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject
            hom)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeSecondObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom

/-- The third vertex of a bounded analytic mapping-cone triangle is transported
by the full-from-geometric recognition functor to the corresponding third
geometric vertex in the full Boundary-DMgm target. -/
def TraceAnalyticMotiveRecognition.weightTriangularMappingConeThirdObjectIso
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
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject
          hom) ≅
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        (homotopyFunctor.obj
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject
            hom)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeThirdObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom

/-- The shifted first vertex of a bounded analytic mapping-cone triangle is
transported by the full-from-geometric recognition functor to the corresponding
shifted first geometric vertex in the full Boundary-DMgm target. -/
def TraceAnalyticMotiveRecognition.weightTriangularMappingConeShiftedFirstObjectIso
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
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject
          hom) ≅
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        (homotopyFunctor.obj
          ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
            hom)⟦(1 : ℤ)⟧)) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeShiftedFirstObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom

/-- The first-vertex mapping-cone weight-triangular object isomorphism is the
existing first-vertex mapping-cone descent comparison isomorphism. -/
theorem TraceAnalyticMotiveRecognition.weightTriangularMappingConeFirstObjectIso_eq
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
    TraceAnalyticMotiveRecognition.weightTriangularMappingConeFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom :=
  rfl

/-- The second-vertex mapping-cone weight-triangular object isomorphism is the
existing second-vertex mapping-cone descent comparison isomorphism. -/
theorem TraceAnalyticMotiveRecognition.weightTriangularMappingConeSecondObjectIso_eq
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
    TraceAnalyticMotiveRecognition.weightTriangularMappingConeSecondObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeSecondObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom :=
  rfl

/-- The third-vertex mapping-cone weight-triangular object isomorphism is the
existing third-vertex mapping-cone descent comparison isomorphism. -/
theorem TraceAnalyticMotiveRecognition.weightTriangularMappingConeThirdObjectIso_eq
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
    TraceAnalyticMotiveRecognition.weightTriangularMappingConeThirdObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeThirdObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom :=
  rfl

/-- The shifted-first mapping-cone weight-triangular object isomorphism is the
existing shifted-first mapping-cone descent comparison isomorphism. -/
theorem TraceAnalyticMotiveRecognition.weightTriangularMappingConeShiftedFirstObjectIso_eq
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
    TraceAnalyticMotiveRecognition.weightTriangularMappingConeShiftedFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeShiftedFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom :=
  rfl

/-- The first map of a bounded analytic mapping-cone triangle satisfies the
weight-triangular naturality square for the full-from-geometric recognition
functor. -/
theorem TraceAnalyticMotiveRecognition.weightTriangular_mappingConeFirstMap_naturality
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
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeFirstMap_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom

/-- The second map of a bounded analytic mapping-cone triangle satisfies the
weight-triangular naturality square for the full-from-geometric recognition
functor. -/
theorem TraceAnalyticMotiveRecognition.weightTriangular_mappingConeSecondMap_naturality
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
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeSecondMap_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom

/-- The connecting map of a bounded analytic mapping-cone triangle satisfies
the weight-triangular naturality square for the full-from-geometric
recognition functor. -/
theorem TraceAnalyticMotiveRecognition.weightTriangular_mappingConeConnectingMap_naturality
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
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeConnectingMap_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom

end AnalyticMotives
end LFunctions
end Boundary
