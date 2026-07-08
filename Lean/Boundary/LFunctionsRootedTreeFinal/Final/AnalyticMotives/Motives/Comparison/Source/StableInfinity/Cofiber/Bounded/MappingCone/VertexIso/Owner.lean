import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Bounded.MappingCone.Vertices.Owner

/-!
# Vertex isomorphisms for chosen cofibers and bounded mapping cones

This file packages the first and second vertex equalities between the chosen
stable-infinity cofiber triangle of a bounded source map and the concrete
stable mapping-cone triangle as categorical isomorphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- First-vertex isomorphism from the chosen stable-infinity cofiber triangle
to the concrete stable bounded mapping-cone triangle. -/
def stableInfinityCofiberTriangleObj₁IsoStableMappingConeTriangleObj₁
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₁ ≅
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle hom).obj₁ :=
  eqToIso
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_obj₁_eq_stableMappingConeTriangle_obj₁
        hom)

/-- Second-vertex isomorphism from the chosen stable-infinity cofiber triangle
to the concrete stable bounded mapping-cone triangle. -/
def stableInfinityCofiberTriangleObj₂IsoStableMappingConeTriangleObj₂
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₂ ≅
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle hom).obj₂ :=
  eqToIso
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_obj₂_eq_stableMappingConeTriangle_obj₂
        hom)

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
