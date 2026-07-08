import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.WeightTriangular.MappingCone.Owner

/-!
# Mapping-cone object isomorphism data for recognition

This file packages transported full faithfulness together with the four
mapping-cone vertex comparison isomorphisms from the weight-triangular
recognition surface.
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

/-- Fully faithful recognition data together with the four object isomorphisms
for a bounded analytic mapping-cone triangle. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeObjectIsos
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
      (composition := composition) twistData homotopyFunctor inverts).FullyFaithful ×
    (((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
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
            hom))) ×
    (((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
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
            hom))) ×
    (((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
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
            hom))) ×
    ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
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
            hom)⟦(1 : ℤ)⟧))))) :=
  Prod.mk
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful)
    (Prod.mk
      (TraceAnalyticMotiveRecognition.weightTriangularMappingConeFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom)
      (Prod.mk
        (TraceAnalyticMotiveRecognition.weightTriangularMappingConeSecondObjectIso
          (composition := composition)
          twistData
          homotopyFunctor
          inverts
          hom)
        (Prod.mk
          (TraceAnalyticMotiveRecognition.weightTriangularMappingConeThirdObjectIso
            (composition := composition)
            twistData
            homotopyFunctor
            inverts
            hom)
          (TraceAnalyticMotiveRecognition.weightTriangularMappingConeShiftedFirstObjectIso
            (composition := composition)
            twistData
            homotopyFunctor
            inverts
            hom))))

/-- The first projection of mapping-cone object recognition data is transported
full faithfulness. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeObjectIsos_fullyFaithful
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeObjectIsos
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).1 =
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful :=
  rfl

/-- The first vertex isomorphism projected from mapping-cone object recognition
data. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeObjectIsos_first
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeObjectIsos
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).2.1 =
    TraceAnalyticMotiveRecognition.weightTriangularMappingConeFirstObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      hom :=
  rfl

/-- The second vertex isomorphism projected from mapping-cone object
recognition data. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeObjectIsos_second
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeObjectIsos
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).2.2.1 =
    TraceAnalyticMotiveRecognition.weightTriangularMappingConeSecondObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      hom :=
  rfl

/-- The third vertex isomorphism projected from mapping-cone object recognition
data. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeObjectIsos_third
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeObjectIsos
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).2.2.2.1 =
    TraceAnalyticMotiveRecognition.weightTriangularMappingConeThirdObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      hom :=
  rfl

/-- The shifted first vertex isomorphism projected from mapping-cone object
recognition data. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeObjectIsos_shiftedFirst
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
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeObjectIsos
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).2.2.2.2 =
    TraceAnalyticMotiveRecognition.weightTriangularMappingConeShiftedFirstObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
