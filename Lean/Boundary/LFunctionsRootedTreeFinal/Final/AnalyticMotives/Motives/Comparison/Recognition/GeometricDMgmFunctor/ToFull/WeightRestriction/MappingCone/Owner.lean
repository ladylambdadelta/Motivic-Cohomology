import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Weights.Bounded.MappingCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightRestriction.Bounded.Owner

/-!
# Bounded mapping-cone restriction of full recognition functors

This file specializes the full Boundary-DMgm recognition functor induced from
geometric recognition data to the stable vertices and stable maps of bounded
analytic mapping-cone comparison data.
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

/-- First-vertex comparison isomorphism for a bounded analytic mapping-cone
triangle under the full-from-geometric recognition functor. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeFirstObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeFirstObjectIso
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

/-- Second-vertex comparison isomorphism for a bounded analytic mapping-cone
triangle under the full-from-geometric recognition functor. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeSecondObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso
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

/-- Third-vertex comparison isomorphism for a bounded analytic mapping-cone
triangle under the full-from-geometric recognition functor. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeThirdObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeThirdObjectIso
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

/-- Shifted-first-vertex comparison isomorphism for a bounded analytic
mapping-cone triangle under the full-from-geometric recognition functor. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeShiftedFirstObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeShiftedFirstObjectIso
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

/-- The full-from-geometric first-vertex mapping-cone comparison isomorphism
is the Boundary-DMgm mapping-cone descent projection for the postcomposed
homotopy functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeFirstObjectIso_eq_descended
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
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeFirstObjectIso
        (composition := composition)
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData)
        (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
          (composition := composition)
          twistData
          homotopyFunctor
          inverts)
        hom :=
  rfl

/-- The full-from-geometric second-vertex mapping-cone comparison isomorphism
is the Boundary-DMgm mapping-cone descent projection for the postcomposed
homotopy functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeSecondObjectIso_eq_descended
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
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeSecondObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData)
        (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
          (composition := composition)
          twistData
          homotopyFunctor
          inverts)
        hom :=
  rfl

/-- The full-from-geometric third-vertex mapping-cone comparison isomorphism
is the Boundary-DMgm mapping-cone descent projection for the postcomposed
homotopy functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeThirdObjectIso_eq_descended
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
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeThirdObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData)
        (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
          (composition := composition)
          twistData
          homotopyFunctor
          inverts)
        hom :=
  rfl

/-- The full-from-geometric shifted-first mapping-cone comparison isomorphism
is the Boundary-DMgm mapping-cone descent projection for the postcomposed
homotopy functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeShiftedFirstObjectIso_eq_descended
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
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeShiftedFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeShiftedFirstObjectIso
        (composition := composition)
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData)
        (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
          (composition := composition)
          twistData
          homotopyFunctor
          inverts)
        hom :=
  rfl

/-- Naturality of the full-from-geometric recognition functor on the first
stable map of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeFirstMap_naturality
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
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeSecondObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeFirstObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mappingConeFirstMap_naturality
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

/-- Naturality of the full-from-geometric recognition functor on the second
stable map of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeSecondMap_naturality
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
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeThirdObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeSecondObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mappingConeSecondMap_naturality
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

/-- Naturality of the full-from-geometric recognition functor on the stable
connecting map of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_mappingConeConnectingMap_naturality
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
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeShiftedFirstObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        hom).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricMappingConeThirdObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mappingConeConnectingMap_naturality
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
