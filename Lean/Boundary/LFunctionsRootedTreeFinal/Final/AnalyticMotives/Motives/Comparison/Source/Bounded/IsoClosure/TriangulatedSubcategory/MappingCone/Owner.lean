import Mathlib.CategoryTheory.Triangulated.Subcategory
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Triangles.MappingCone.Triangle.IsoClosure.Owner

/-!
# Mapping-cone input for the iso-closure bounded triangulated subcategory

This file exposes the concrete bounded analytic mapping-cone triangle as the
cone-closure input for the degreewise iso-closure bounded stable-source
predicate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceBoundedMappingCone

/-- The third vertex of a stable bounded analytic mapping-cone triangle belongs
to the iso-closure of the degreewise iso-closure bounded stable-source
predicate. -/
theorem stableTriangle_obj₃_mem_isoClosure_degreewiseIsoClosureBoundedStableObject
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
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle hom).obj₃ :=
  CategoryTheory.le_isoClosure
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle hom).obj₃
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle_obj₃_degreewiseIsoClosureBoundedStableObject hom)

/-- The stable bounded analytic mapping-cone triangle is a distinguished
triangle whose third vertex lies in the iso-closure of the degreewise
iso-closure bounded stable-source predicate. -/
theorem stableTriangle_distinguished_with_obj₃_isoClosure
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle hom ∈
      Pretriangulated.distTriang TraceAnalyticDMgmComparisonSource) ∧
      CategoryTheory.isoClosure
        TraceAnalyticDMgmComparisonSource
          .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableTriangle hom).obj₃ :=
  And.intro
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle_distinguished hom)
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle_obj₃_mem_isoClosure_degreewiseIsoClosureBoundedStableObject
        hom)

end SourceBoundedMappingCone
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
