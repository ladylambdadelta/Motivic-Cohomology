import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.NaturalTransformations.Naturality.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Stable.Owner

/-!
# Geometric Boundary DMgm descended naturality for bounded mapping cones

This file specializes geometric descended-natural-transformation naturality to
the three stable maps of bounded analytic mapping-cone comparison data.
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

/-- Naturality of a geometric Boundary-DMgm descended natural transformation on
the first stable map of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_mappingConeFirstMap_naturality
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
          hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstMap
            hom) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstMap
            hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
            hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstMap hom)

/-- Naturality of a geometric Boundary-DMgm descended natural transformation on
the second stable map of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_mappingConeSecondMap_naturality
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
          hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondMap
            hom) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondMap
            hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject
            hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondMap hom)

/-- Naturality of a geometric Boundary-DMgm descended natural transformation on
the stable connecting map of a bounded analytic mapping-cone triangle. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_mappingConeConnectingMap_naturality
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
          hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableConnectingMap
            hom) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableConnectingMap
            hom) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject
            hom) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.connectingMap hom)

end AnalyticMotives
end LFunctions
end Boundary
