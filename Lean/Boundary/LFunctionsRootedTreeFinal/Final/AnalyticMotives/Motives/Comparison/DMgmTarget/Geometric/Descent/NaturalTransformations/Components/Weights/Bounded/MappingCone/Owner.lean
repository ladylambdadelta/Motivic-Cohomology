import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.NaturalTransformations.Components.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Weights.Bounded.MappingCone.Owner

/-!
# Components of geometric descended transformations on mapping-cone vertices

This file specializes geometric descended-natural-transformation component
formulas to the stable vertices of bounded analytic mapping-cone comparison
data.
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

/-- Component formula for a geometric Boundary-DMgm descended natural
transformation at the first stable vertex of a bounded analytic mapping-cone
triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_mappingConeFirstObject
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
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom)

/-- Component formula for a geometric Boundary-DMgm descended natural
transformation at the second stable vertex of a bounded analytic mapping-cone
triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_mappingConeSecondObject
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
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject hom)

/-- Component formula for a geometric Boundary-DMgm descended natural
transformation at the third stable vertex of a bounded analytic mapping-cone
triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_mappingConeThirdObject
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
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject
          hom) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        hom).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        hom).inv :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject hom)

/-- Component formula for a geometric Boundary-DMgm descended natural
transformation at the shifted first stable vertex of a bounded analytic
mapping-cone triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_mappingConeShiftedFirstObject
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
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject
          hom) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeShiftedFirstObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        hom).hom ≫
      transformation.app
        ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
          hom)⟦(1 : ℤ)⟧) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorMappingConeShiftedFirstObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        hom).inv :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom)⟦(1 : ℤ)⟧)

end AnalyticMotives
end LFunctions
end Boundary
