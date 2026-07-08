import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Bounded.Vertices.Owner

/-!
# Fiber triangle isomorphism for bounded mapping cones

This file identifies the chosen stable-infinity fiber triangle of a bounded
source map with the inverse rotation of the concrete stable bounded
mapping-cone triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- The chosen stable-infinity fiber triangle of a bounded source map is
isomorphic to the inverse rotation of the concrete stable bounded mapping-cone
triangle. -/
def stableInfinityFiberTriangleIsoInvRotateStableMappingConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ≅
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle hom).invRotate :=
  eqToIso
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle_eq_invRotate_cofiber
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)) ≪≫
    (Pretriangulated.invRotate
      TraceAnalyticDMgmComparisonSource).mapIso
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
          .stableInfinityCofiberTriangleIsoStableMappingConeTriangle
            hom)

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
