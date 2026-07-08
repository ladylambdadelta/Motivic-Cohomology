import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Stable.Owner

/-!
# Boundary DMgm descent projections for bounded mapping-cone data

This file specializes represented-object and represented-map descent
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

/-- Object projection for the first stable vertex of a bounded analytic
mapping-cone triangle after descent to the Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeFirstObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
          hom) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
          hom) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom)

/-- Object projection for the second stable vertex of a bounded analytic
mapping-cone triangle after descent to the Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
          hom) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject
          hom) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject hom)

/-- Object projection for the third stable vertex of a bounded analytic
mapping-cone triangle after descent to the Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeThirdObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject
          hom) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject
          hom) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject hom)

/-- Object projection for the shifted first stable vertex of a bounded
analytic mapping-cone triangle after descent to the Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeShiftedFirstObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject
          hom) ≅
      functor.obj
        ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
          hom)⟦(1 : ℤ)⟧) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
    (composition := composition)
    functor
    inverts
    ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom)⟦(1 : ℤ)⟧)

/-- The first mapping-cone object projection is the general quotient-object
projection at the first additive-homotopy vertex. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeFirstObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeFirstObjectIso
        (composition := composition)
        functor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom) :=
  rfl

/-- The second mapping-cone object projection is the general quotient-object
projection at the second additive-homotopy vertex. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        functor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject hom) :=
  rfl

/-- The third mapping-cone object projection is the general quotient-object
projection at the third additive-homotopy vertex. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeThirdObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        functor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject hom) :=
  rfl

/-- The shifted first mapping-cone object projection is the general
quotient-object projection at the shifted first additive-homotopy vertex. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeShiftedFirstObjectIso_eq
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeShiftedFirstObjectIso
        (composition := composition)
        functor
        inverts
        hom =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
          hom)⟦(1 : ℤ)⟧) :=
  rfl

/-- Morphism projection for the first stable map of a bounded analytic
mapping-cone triangle after descent to the Boundary DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mappingConeFirstMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstMap
          hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        functor
        inverts
        hom).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeFirstObjectIso
        (composition := composition)
        functor
        inverts
        hom).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstMap hom) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstMap hom)

/-- Morphism projection for the second stable map of a bounded analytic
mapping-cone triangle after descent to the Boundary DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mappingConeSecondMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondMap
          hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        functor
        inverts
        hom).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        functor
        inverts
        hom).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondMap hom) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondMap hom)

/-- Morphism projection for the stable connecting map of a bounded analytic
mapping-cone triangle after descent to the Boundary DMgm target. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mappingConeConnectingMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
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
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableConnectingMap
          hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeShiftedFirstObjectIso
        (composition := composition)
        functor
        inverts
        hom).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        functor
        inverts
        hom).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.connectingMap hom) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.connectingMap hom)

end AnalyticMotives
end LFunctions
end Boundary
