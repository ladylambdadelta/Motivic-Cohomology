import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.NaturalTransformations.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.BoundedDescent.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.BoundedDescent.Projections.Owner

/-!
# Bounded descent endpoint surface

This file collects bounded, shifted bounded, and bounded mapping-cone descent
projection, component, and naturality statements for both concrete and
geometric Boundary DMgm targets under comparison-facing names.
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

/-- Endpoint wrapper: concrete Boundary-DMgm descent is natural on stable maps
represented by bounded analytic chain maps. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_boundedMap_naturality
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
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        functor
        inverts
        target).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        functor
        inverts
        source).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_boundedMap_naturality
    (composition := composition)
    functor
    inverts
    hom

/-- Endpoint wrapper: concrete Boundary-DMgm descent is natural on stable
shifted maps represented by bounded analytic chain maps. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_shiftedBoundedMap_naturality
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
        target)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
          hom
          degree) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        functor
        inverts
        target
        degree).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        functor
        inverts
        source
        degree).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
            hom
            degree) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_shiftedBoundedMap_naturality
    (composition := composition)
    functor
    inverts
    hom
    degree

/-- Endpoint wrapper: concrete Boundary-DMgm descent is natural on the first
stable map of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_mappingConeFirstMap_naturality
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mappingConeFirstMap_naturality
    (composition := composition)
    functor
    inverts
    hom

/-- Endpoint wrapper: geometric Boundary-DMgm descent is natural on stable maps
represented by bounded analytic chain maps. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_boundedMap_naturality
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
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
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        target).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        source).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_boundedMap_naturality
    (composition := composition)
    twistData
    functor
    inverts
    hom

/-- Endpoint wrapper: geometric Boundary-DMgm descent is natural on stable
shifted maps represented by bounded analytic chain maps. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_shiftedBoundedMap_naturality
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
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
        target)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
          hom
          degree) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        target
        degree).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        source
        degree).hom ≫
        functor.map
          (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
            hom
            degree) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_shiftedBoundedMap_naturality
    (composition := composition)
    twistData
    functor
    inverts
    hom
    degree

/-- Endpoint wrapper: geometric Boundary-DMgm descent is natural on the first
stable map of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_mappingConeFirstMap_naturality
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
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
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mappingConeFirstMap_naturality
    (composition := composition)
    twistData
    functor
    inverts
    hom

end AnalyticMotives
end LFunctions
end Boundary
