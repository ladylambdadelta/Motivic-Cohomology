import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Bounded.Vertices.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Stable.Triangle.Owner

/-!
# First-map comparison for chosen cofibers and bounded mapping cones

This file records that the chosen stable-infinity cofiber triangle of a
bounded source map and the concrete stable mapping-cone triangle have the same
first morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- The first morphism of the stable bounded mapping-cone triangle is the
bounded source map. -/
theorem stableMappingConeTriangle_mor₁_eq_sourceStableWeightBoundedMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle hom).mor₁ =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle_mor₁ hom)
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableFirstMap_eq hom)

/-- The chosen stable-infinity cofiber triangle and the concrete stable
bounded mapping-cone triangle of a bounded source map have the same first
morphism. -/
theorem stableInfinityCofiberTriangle_mor₁_eq_stableMappingConeTriangle_mor₁
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).mor₁ =
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle hom).mor₁ :=
  Eq.trans
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle_mor₁
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom))
    (Eq.symm
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableMappingConeTriangle_mor₁_eq_sourceStableWeightBoundedMap hom))

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
