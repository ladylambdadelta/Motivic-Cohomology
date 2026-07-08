import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Stable.Owner

/-!
# Geometric Boundary DMgm descent projections for bounded mapping cones

This file specializes geometric represented-object and represented-map descent
projections to the vertices and morphisms of a bounded analytic mapping-cone
triangle.
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

/-- Object projection for the first stable vertex of a bounded analytic
mapping-cone triangle after descent to the geometric Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeFirstObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
          hom) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
          hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom)

/-- Object projection for the second stable vertex of a bounded analytic
mapping-cone triangle after descent to the geometric Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeSecondObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
          hom) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject
          hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject hom)

/-- Object projection for the third stable vertex of a bounded analytic
mapping-cone triangle after descent to the geometric Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeThirdObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject
          hom) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject
          hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject hom)

/-- Object projection for the shifted first stable vertex of a bounded analytic
mapping-cone triangle after descent to the geometric Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeShiftedFirstObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject
          hom) ≅
      functor.obj
        ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
          hom)⟦(1 : ℤ)⟧) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom)⟦(1 : ℤ)⟧)

/-- The first geometric mapping-cone object projection is the general
quotient-object projection at the first additive-homotopy vertex. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeFirstObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeFirstObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom) :=
  rfl

/-- The second geometric mapping-cone object projection is the general
quotient-object projection at the second additive-homotopy vertex. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeSecondObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject hom) :=
  rfl

/-- The third geometric mapping-cone object projection is the general
quotient-object projection at the third additive-homotopy vertex. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeThirdObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject hom) :=
  rfl

/-- The shifted first geometric mapping-cone object projection is the general
quotient-object projection at the shifted first additive-homotopy vertex. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeShiftedFirstObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeShiftedFirstObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
          hom)⟦(1 : ℤ)⟧) :=
  rfl

/-- Morphism projection for the first stable map of a bounded analytic
mapping-cone triangle after descent to the geometric Boundary DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mappingConeFirstMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstMap
          hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeFirstObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstMap hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstMap hom)

/-- Morphism projection for the second stable map of a bounded analytic
mapping-cone triangle after descent to the geometric Boundary DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mappingConeSecondMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondMap
          hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondMap hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondMap hom)

/-- Morphism projection for the stable connecting map of a bounded analytic
mapping-cone triangle after descent to the geometric Boundary DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mappingConeConnectingMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableConnectingMap
          hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeShiftedFirstObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        hom).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.connectingMap hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.connectingMap hom)

end AnalyticMotives
end LFunctions
end Boundary
