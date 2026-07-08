import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Shift.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Owner

/-!
# Shifts of bounded analytic mapping-cone triangles

Mathlib identifies the shift of a mapping-cone triangle with the mapping-cone
triangle of the shifted map.  This file exposes that comparison for bounded
analytic chain maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The concrete shifted mapping-cone complex represents the third object of the
mapping-cone triangle of the shifted bounded map. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdRepresentativeIsoShiftedMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.objectOf
        ((CochainComplex.shiftFunctor TraceAnalyticAdditiveCategoryObject shift).obj
          (CochainComplex.mappingCone hom)) ≅
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (hom.shift shift) :=
  TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.mapIso
    (CochainComplex.mappingCone.shiftIso hom shift)

/-- The shifted representative comparison is Mathlib's shifted mapping-cone isomorphism
sent through the homotopy quotient. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdRepresentativeIsoShiftedMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdRepresentativeIsoShiftedMap
        hom
        shift =
      TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.mapIso
        (CochainComplex.mappingCone.shiftIso hom shift) :=
  rfl

/-- The shifted third object of a bounded mapping-cone triangle is canonically
isomorphic to the third object of the mapping-cone triangle of the shifted map. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectIsoShiftedMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedObject
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject hom)
        shift ≅
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (hom.shift shift) :=
  ((TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.commShiftIso
      shift).app
    (CochainComplex.mappingCone hom)).symm ≪≫
    TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.mapIso
      (CochainComplex.mappingCone.shiftIso hom shift)

/-- The shifted-third-object comparison is the quotient shift comparison followed by
Mathlib's shifted mapping-cone isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectIsoShiftedMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedThirdObjectIsoShiftedMap
        hom
        shift =
      ((TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.commShiftIso
          shift).app
        (CochainComplex.mappingCone hom)).symm ≪≫
        TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.mapIso
          (CochainComplex.mappingCone.shiftIso hom shift) :=
  rfl

/-- The shifted mapping-cone triangle is canonically isomorphic to the mapping-cone
triangle of the shifted bounded map. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom).shiftedTriangle shift ≅
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (hom.shift shift) :=
  CochainComplex.mappingCone.shiftTrianglehIso hom shift

/-- The shifted-triangle comparison is Mathlib's shifted mapping-cone triangle isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
        hom
        shift =
      CochainComplex.mappingCone.shiftTrianglehIso hom shift :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
