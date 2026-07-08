import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Components.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Weights.Bounded.MappingCone.Owner

/-!
# Components of descended transformations on bounded mapping-cone vertices

This file specializes descended-natural-transformation component formulas to
the stable vertices of bounded analytic mapping-cone comparison data.
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

/-- Component formula for a Boundary-DMgm descended natural transformation at
the first stable vertex of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_mappingConeFirstObject
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom)

/-- Component formula for a Boundary-DMgm descended natural transformation at
the second stable vertex of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_mappingConeSecondObject
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject hom)

/-- Component formula for a Boundary-DMgm descended natural transformation at
the third stable vertex of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_mappingConeThirdObject
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
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject
          hom) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        first
        firstInverts
        hom).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject hom) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeThirdObjectIso
        (composition := composition)
        second
        secondInverts
        hom).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject hom)

/-- Component formula for a Boundary-DMgm descended natural transformation at
the shifted first stable vertex of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_mappingConeShiftedFirstObject
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
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject
          hom) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeShiftedFirstObjectIso
        (composition := composition)
        first
        firstInverts
        hom).hom ≫
      transformation.app
        ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
          hom)⟦(1 : ℤ)⟧) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorMappingConeShiftedFirstObjectIso
        (composition := composition)
        second
        secondInverts
        hom).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom)⟦(1 : ℤ)⟧)

end AnalyticMotives
end LFunctions
end Boundary
