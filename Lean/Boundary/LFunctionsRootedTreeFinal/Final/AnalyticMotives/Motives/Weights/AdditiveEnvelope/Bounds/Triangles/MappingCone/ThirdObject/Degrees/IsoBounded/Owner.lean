import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.DegreewiseRepresentative.IsoBounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.DegreewiseRepresentative.Owner

/-!
# Iso-bounded degrees of bounded mapping-cone third vertices

Every degree object of the concrete mapping-cone complex representing the third
vertex is bounded up to the explicitly constructed analytic isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Each actual mapping-cone degree object is iso-bounded by the cone bound. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoBounded
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject.IsoBoundedBy
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegree
        hom
        degree)
      bound :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.degreewiseBoundedRepresentative
    hom).degreeIsoBounded degree

/-- The bounded representative of a cone degree is the standard cone-degree object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoBounded_representative
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoBounded
      hom
      degree).boundedRepresentative =
      hom.mappingConeDegreeObject degree :=
  rfl

/-- The bounded representative of a cone degree satisfies the ambient bound. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoBounded_weightLevel_le
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoBounded
      hom
      degree).boundedRepresentative.object.weightLevel ≤ bound :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoBounded
    hom
    degree).representative_weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
