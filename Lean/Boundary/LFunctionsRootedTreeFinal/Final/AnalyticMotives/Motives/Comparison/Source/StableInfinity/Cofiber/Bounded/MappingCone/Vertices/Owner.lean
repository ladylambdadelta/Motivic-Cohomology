import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Bounded.MappingCone.FirstMap.Owner

/-!
# Vertex comparison for chosen cofibers and bounded mapping cones

This file records that the chosen stable-infinity cofiber triangle of a
bounded source map and the concrete stable mapping-cone triangle have the same
first two vertices.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- The first vertex of the chosen stable-infinity cofiber triangle of a
bounded source map is the first vertex of the concrete stable mapping-cone
triangle. -/
theorem stableInfinityCofiberTriangle_obj₁_eq_stableMappingConeTriangle_obj₁
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₁ =
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle hom).obj₁ :=
  Eq.trans
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle_obj₁
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom))
    (Eq.symm
      (Eq.trans
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableTriangle_obj₁ hom)
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableFirstObject_eq hom)))

/-- The second vertex of the chosen stable-infinity cofiber triangle of a
bounded source map is the second vertex of the concrete stable mapping-cone
triangle. -/
theorem stableInfinityCofiberTriangle_obj₂_eq_stableMappingConeTriangle_obj₂
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₂ =
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle hom).obj₂ :=
  Eq.trans
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle_obj₂
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom))
    (Eq.symm
      (Eq.trans
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableTriangle_obj₂ hom)
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableSecondObject_eq hom)))

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
