import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Summary.Owner

/-!
# Bounded descent endpoint projection isomorphisms

This file collects object projection isomorphisms for bounded, shifted bounded,
and bounded mapping-cone analytic objects after descent to concrete and
geometric Boundary DMgm targets.
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

/-- Endpoint projection isomorphism for concrete Boundary-DMgm descent on a
stable bounded analytic object. -/
def TraceAnalyticMotiveComparison.concreteTarget_boundedObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
    (composition := composition)
    functor
    inverts
    complex

/-- Endpoint projection isomorphism for concrete Boundary-DMgm descent on a
stable shifted bounded analytic object. -/
def TraceAnalyticMotiveComparison.concreteTarget_shiftedBoundedObjectIso
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
    (composition := composition)
    functor
    inverts
    complex
    degree

/-- Endpoint projection isomorphism for the first stable bounded mapping-cone
vertex after concrete Boundary-DMgm descent. -/
def TraceAnalyticMotiveComparison.concreteTarget_mappingConeFirstObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeFirstObjectIso
    (composition := composition)
    functor
    inverts
    hom

/-- Endpoint projection isomorphism for the second stable bounded mapping-cone
vertex after concrete Boundary-DMgm descent. -/
def TraceAnalyticMotiveComparison.concreteTarget_mappingConeSecondObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso
    (composition := composition)
    functor
    inverts
    hom

/-- Endpoint projection isomorphism for geometric Boundary-DMgm descent on a
stable bounded analytic object. -/
def TraceAnalyticMotiveComparison.geometricTarget_boundedObjectIso
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
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    complex

/-- Endpoint projection isomorphism for geometric Boundary-DMgm descent on a
stable shifted bounded analytic object. -/
def TraceAnalyticMotiveComparison.geometricTarget_shiftedBoundedObjectIso
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
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).obj
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    complex
    degree

/-- Endpoint projection isomorphism for the first stable bounded mapping-cone
vertex after geometric Boundary-DMgm descent. -/
def TraceAnalyticMotiveComparison.geometricTarget_mappingConeFirstObjectIso
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
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
          hom) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
          hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeFirstObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    hom

/-- Endpoint projection isomorphism for the second stable bounded mapping-cone
vertex after geometric Boundary-DMgm descent. -/
def TraceAnalyticMotiveComparison.geometricTarget_mappingConeSecondObjectIso
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
      inverts).obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
          hom) ≅
      functor.obj
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject
          hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeSecondObjectIso
    (composition := composition)
    twistData
    functor
    inverts
    hom

end AnalyticMotives
end LFunctions
end Boundary
