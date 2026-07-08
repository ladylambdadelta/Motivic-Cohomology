import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Owner

/-!
# Stable images of bounded mapping-cone comparison data

This file sends the vertices and morphisms of a bounded analytic mapping-cone
triangle through the stable analytic comparison-source quotient.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Stable comparison-source image of the first vertex of a bounded
mapping-cone triangle. -/
def TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject hom)

/-- Stable comparison-source image of the second vertex of a bounded
mapping-cone triangle. -/
def TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject hom)

/-- Stable comparison-source image of the third vertex of a bounded
mapping-cone triangle. -/
def TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject hom)

/-- Stable comparison-source image of the shifted first vertex of a bounded
mapping-cone triangle. -/
def TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf
    ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject
      hom)⟦(1 : ℤ)⟧)

/-- Stable comparison-source image of the first map of a bounded mapping-cone
triangle. -/
def TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject hom ⟶
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject hom :=
  TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstMap hom)

/-- Stable comparison-source image of the second map of a bounded mapping-cone
triangle. -/
def TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject hom ⟶
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject hom :=
  TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondMap hom)

/-- Stable comparison-source image of the connecting map of a bounded
mapping-cone triangle. -/
def TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableConnectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject hom ⟶
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject hom :=
  TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.connectingMap hom)

/-- The stable first vertex is the stable bounded source object. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject hom =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject source :=
  congrArg
    TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject_eq hom)

/-- The stable second vertex is the stable bounded target object. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject hom =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject target :=
  congrArg
    TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondObject_eq hom)

/-- The stable third vertex is the stable image of the concrete mapping-cone
complex. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject hom =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          (CochainComplex.mappingCone hom)) :=
  congrArg
    TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.thirdObject_eq hom)

/-- The stable shifted first vertex is the stable image of the shifted bounded
source homotopy object. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableShiftedFirstObject hom =
      TraceAnalyticDMgmComparisonSource.objectOf
        ((TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          source)⟦(1 : ℤ)⟧) :=
  congrArg
    (fun object =>
      TraceAnalyticDMgmComparisonSource.objectOf (object⟦(1 : ℤ)⟧))
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstObject_eq hom)

/-- The stable first map is the stable bounded source map. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstMap hom =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom :=
  congrArg
    TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.firstMap_eq hom)

/-- The stable second map is the stable image of the cone-inclusion map into
the concrete mapping-cone complex. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondMap hom =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticAdditiveHomotopyCategory.mapOf
          (CochainComplex.mappingCone.inr hom)) :=
  congrArg
    TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.secondMap_eq hom)

/-- The stable connecting map is the stable image of the third morphism of the
bounded mapping-cone triangle. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableConnectingMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableConnectingMap hom =
      TraceAnalyticDMgmComparisonSource.mapOf
        ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone.triangle
          hom).mor₃) :=
  congrArg
    TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.connectingMap_eq hom)

/-- Rebounding the bounded source representative does not change the stable
first vertex. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy lower}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
        (hom.rebound bound_le) =
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
        hom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject_eq
      (hom.rebound bound_le))
    (Eq.trans
      (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject_rebound
        bound_le
        source
      )
      (Eq.symm
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject_eq
          hom)))

/-- Rebounding the bounded target representative does not change the stable
second vertex. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy lower}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
        (hom.rebound bound_le) =
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
        hom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject_eq
      (hom.rebound bound_le))
    (Eq.trans
      (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject_rebound
        bound_le
        target
      )
      (Eq.symm
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject_eq
          hom)))

end AnalyticMotives
end LFunctions
end Boundary
