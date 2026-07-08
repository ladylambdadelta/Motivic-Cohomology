import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Bounded.MappingCone.TriangleIso.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.IsoClosure.TriangulatedSubcategory.MappingCone.Owner

/-!
# Third vertex transfer for chosen cofibers and bounded mapping cones

This file transfers the concrete bounded mapping-cone third-vertex membership
across the triangle isomorphism to the chosen stable-infinity cofiber triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- The third vertex of the chosen stable-infinity cofiber triangle of a
bounded source map belongs to the iso-closure of the bounded stable analytic
source predicate. -/
theorem stableInfinityCofiberTriangle_obj₃_mem_isoClosure_degreewiseIsoClosureBoundedStableObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    CategoryTheory.isoClosure
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₃ :=
  CategoryTheory.mem_of_iso
    (CategoryTheory.isoClosure
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject)
    (Triangle.π₃.mapIso
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableInfinityCofiberTriangleIsoStableMappingConeTriangle
          hom)).symm
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle_obj₃_mem_isoClosure_degreewiseIsoClosureBoundedStableObject
        hom)

/-- The chosen stable-infinity cofiber triangle of a bounded source map is
distinguished and all three vertices are controlled by the bounded stable
analytic source predicate, with the cone vertex controlled up to isomorphism. -/
theorem stableInfinityCofiberTriangle_distinguished_with_bounded_vertices
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ∈
      Pretriangulated.distTriang TraceAnalyticDMgmComparisonSource) ∧
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityCofiberTriangle
              (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₁ ∧
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityCofiberTriangle
              (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₂ ∧
      CategoryTheory.isoClosure
        TraceAnalyticDMgmComparisonSource
          .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangle
            (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₃ :=
  And.intro
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_distinguished hom)
    (And.intro
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableInfinityCofiberTriangle_obj₁_degreewiseIsoClosureBoundedStableObject
          hom)
      (And.intro
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
          .stableInfinityCofiberTriangle_obj₂_degreewiseIsoClosureBoundedStableObject
            hom)
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
          .stableInfinityCofiberTriangle_obj₃_mem_isoClosure_degreewiseIsoClosureBoundedStableObject
            hom)))

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
