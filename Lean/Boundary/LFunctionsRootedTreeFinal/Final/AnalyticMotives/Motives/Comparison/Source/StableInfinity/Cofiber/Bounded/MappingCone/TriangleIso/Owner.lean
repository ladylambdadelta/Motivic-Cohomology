import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Bounded.MappingCone.FirstSquare.Owner

/-!
# Triangle isomorphism for chosen cofibers and bounded mapping cones

This file identifies the chosen stable-infinity cofiber triangle of a bounded
source map with the concrete stable bounded mapping-cone triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- The chosen stable-infinity cofiber triangle of a bounded source map is
isomorphic to the concrete stable bounded mapping-cone triangle. -/
def stableInfinityCofiberTriangleIsoStableMappingConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ≅
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle hom :=
  isoTriangleOfIso₁₂
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom))
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_distinguished hom)
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle_distinguished hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangleObj₁IsoStableMappingConeTriangleObj₁
        hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangleObj₂IsoStableMappingConeTriangleObj₂
        hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_firstSquare_stableMappingConeTriangle
        hom)

/-- The triangle isomorphism has the expected first component. -/
theorem stableInfinityCofiberTriangleIsoStableMappingConeTriangle_hom₁
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangleIsoStableMappingConeTriangle hom).hom.hom₁ =
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableInfinityCofiberTriangleObj₁IsoStableMappingConeTriangleObj₁
          hom).hom :=
  isoTriangleOfIso₁₂_hom_hom₁
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom))
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_distinguished hom)
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle_distinguished hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangleObj₁IsoStableMappingConeTriangleObj₁
        hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangleObj₂IsoStableMappingConeTriangleObj₂
        hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_firstSquare_stableMappingConeTriangle
        hom)

/-- The triangle isomorphism has the expected second component. -/
theorem stableInfinityCofiberTriangleIsoStableMappingConeTriangle_hom₂
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangleIsoStableMappingConeTriangle hom).hom.hom₂ =
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableInfinityCofiberTriangleObj₂IsoStableMappingConeTriangleObj₂
          hom).hom :=
  isoTriangleOfIso₁₂_hom_hom₂
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom))
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_distinguished hom)
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableTriangle_distinguished hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangleObj₁IsoStableMappingConeTriangleObj₁
        hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangleObj₂IsoStableMappingConeTriangleObj₂
        hom)
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_firstSquare_stableMappingConeTriangle
        hom)

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
