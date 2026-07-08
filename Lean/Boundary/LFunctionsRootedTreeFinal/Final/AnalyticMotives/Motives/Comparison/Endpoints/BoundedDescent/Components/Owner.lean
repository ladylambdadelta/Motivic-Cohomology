import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.NaturalTransformations.Summary.Owner

/-!
# Bounded descent endpoint component formulas

This file collects component formulas for descended natural transformations on
bounded, shifted bounded, and bounded mapping-cone analytic objects for both
concrete and geometric Boundary DMgm targets.
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

/-- Endpoint wrapper: concrete Boundary-DMgm descended natural transformations
have the bounded-object component formula. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_natTrans_app_boundedObject
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        first
        firstInverts
        complex).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        second
        secondInverts
        complex).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_boundedObject
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    complex

/-- Endpoint wrapper: concrete Boundary-DMgm descended natural transformations
have the shifted bounded-object component formula. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_natTrans_app_shiftedBoundedObject
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        first
        firstInverts
        complex
        degree).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        second
        secondInverts
        complex
        degree).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_shiftedBoundedObject
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    complex
    degree

/-- Endpoint wrapper: concrete Boundary-DMgm descended natural transformations
have component formulas at the first bounded mapping-cone vertex. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_natTrans_app_mappingConeFirstObject
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
          hom) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeFirstObjectIso
        (composition := composition)
        first
        firstInverts
        hom).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeFirstObjectIso
        (composition := composition)
        second
        secondInverts
        hom).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_mappingConeFirstObject
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    hom

/-- Endpoint wrapper: concrete Boundary-DMgm descended natural transformations
have component formulas at the second bounded mapping-cone vertex. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_natTrans_app_mappingConeSecondObject
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
          hom) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        first
        firstInverts
        hom).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        second
        secondInverts
        hom).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_mappingConeSecondObject
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    hom

/-- Endpoint wrapper: geometric Boundary-DMgm descended natural transformations
have the bounded-object component formula. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_natTrans_app_boundedObject
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        complex).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorBoundedObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        complex).inv :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_boundedObject
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    complex

/-- Endpoint wrapper: geometric Boundary-DMgm descended natural transformations
have the shifted bounded-object component formula. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_natTrans_app_shiftedBoundedObject
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        complex
        degree).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        complex
        degree).inv :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_shiftedBoundedObject
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    complex
    degree

/-- Endpoint wrapper: geometric Boundary-DMgm descended natural transformations
have component formulas at the first bounded mapping-cone vertex. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_natTrans_app_mappingConeFirstObject
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
          hom) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeFirstObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        hom).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeFirstObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        hom).inv :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_mappingConeFirstObject
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    hom

/-- Endpoint wrapper: geometric Boundary-DMgm descended natural transformations
have component formulas at the second bounded mapping-cone vertex. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_natTrans_app_mappingConeSecondObject
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
          hom) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        hom).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeSecondObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        hom).inv :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_mappingConeSecondObject
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    hom

end AnalyticMotives
end LFunctions
end Boundary
