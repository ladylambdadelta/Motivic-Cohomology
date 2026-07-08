import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Owner

/-!
# Maps into the bounded analytic mapping-cone third object

The second morphism of a bounded mapping-cone triangle is the homotopy-category
image of Mathlib's right inclusion into the mapping-cone complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The cone-inclusion map from the target object to the mapping-cone third object. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject hom ⟶
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject hom :=
  TraceAnalyticAdditiveHomotopyCategory.mapOf
    (CochainComplex.mappingCone.inr hom)

/-- The cone-inclusion map is the homotopy image of Mathlib's right inclusion. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom =
      TraceAnalyticAdditiveHomotopyCategory.mapOf
        (CochainComplex.mappingCone.inr hom) :=
  rfl

/-- The second morphism of the mapping-cone triangle is the named cone-inclusion map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle_mor₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle hom).mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
