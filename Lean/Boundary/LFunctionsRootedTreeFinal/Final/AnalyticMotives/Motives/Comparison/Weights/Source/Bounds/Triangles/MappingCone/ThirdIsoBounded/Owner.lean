import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.IsoBounded.Owner

/-!
# Source-facing iso-bounded mapping-cone third vertices

This file exposes the degreewise iso-bounded data for the concrete
mapping-cone complex representing the third vertex of a bounded analytic
mapping-cone triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotiveComparison
namespace SourceBoundedMappingCone

/-- The concrete mapping-cone complex representing the third vertex of a
source bounded mapping-cone triangle is degreewise iso-bounded by the same
weight bound. -/
def thirdObjectDegreewiseIsoBounded
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
      (CochainComplex.mappingCone hom)
      bound :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone
    .thirdObjectDegreewiseIsoBounded hom

/-- The source-facing third-vertex iso-bounded datum uses the same bounded
degree representatives as the additive mapping-cone construction. -/
theorem thirdObjectDegreewiseIsoBounded_representative
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (((TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .thirdObjectDegreewiseIsoBounded hom).degreeObject degree)
        .boundedRepresentative) =
      (((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone
        .thirdObjectDegreewiseIsoBounded hom).degreeObject degree)
        .boundedRepresentative) :=
  rfl

/-- The bounded degree representative for the third mapping-cone vertex
satisfies the ambient source weight bound. -/
theorem thirdObjectDegreewiseIsoBounded_weightLevel_le
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (((TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .thirdObjectDegreewiseIsoBounded hom).degreeObject degree)
        .boundedRepresentative).object.weightLevel ≤
      bound :=
  (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
    .thirdObjectDegreewiseIsoBounded hom).degreeObject_weightLevel_le degree

/-- Each actual degree object of the concrete third mapping-cone complex
belongs to the iso-closure of bounded additive objects. -/
theorem thirdObjectDegree_mem_isoClosure_boundedObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative bound)
      ((CochainComplex.mappingCone hom).objectAt degree) :=
  (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
    .thirdObjectDegreewiseIsoBounded hom)
    .degreeObject_mem_isoClosure_boundedObject degree

/-- The concrete third mapping-cone complex is degreewise in the iso-closure
of bounded additive objects. -/
theorem thirdObjectDegreewiseIsoClosureBoundedBy
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
      (CochainComplex.mappingCone hom)
      bound :=
  (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
    .thirdObjectDegreewiseIsoBounded hom)
    .degreewiseIsoClosureBoundedBy

/-- The concrete third mapping-cone complex is comparison-source degreewise
bounded up to iso-closure. -/
theorem thirdObject_sourceDegreewiseIsoClosureBoundedBy
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
      (CochainComplex.mappingCone hom)
      bound :=
  TraceAnalyticMotiveComparison.SourceBoundedMappingCone
    .thirdObjectDegreewiseIsoClosureBoundedBy hom

end SourceBoundedMappingCone
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
