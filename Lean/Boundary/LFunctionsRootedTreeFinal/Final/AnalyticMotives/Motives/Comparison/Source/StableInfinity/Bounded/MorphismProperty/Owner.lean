import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Bounded.MappingCone.ThirdVertex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Bounded.Vertices.Owner

/-!
# Bounded morphism properties from stable-infinity fibers and cofibers

This file names the concrete morphism properties cut out by the chosen
stable-infinity cofiber and fiber triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- A comparison-source morphism has bounded cofiber if the third vertex of
its chosen stable-infinity cofiber triangle belongs to the degreewise
iso-closure bounded stable-source predicate. -/
def cofiberDegreewiseIsoClosureBoundedMorphisms :
    MorphismProperty TraceAnalyticDMgmComparisonSource :=
  fun _ _ morphism =>
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangle morphism).obj₃

/-- A comparison-source morphism has bounded fiber if the first vertex of its
chosen stable-infinity fiber triangle belongs to the degreewise iso-closure
bounded stable-source predicate. -/
def fiberDegreewiseIsoClosureBoundedMorphisms :
    MorphismProperty TraceAnalyticDMgmComparisonSource :=
  fun _ _ morphism =>
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityFiberTriangle morphism).obj₁

end TraceAnalyticDMgmComparisonSource

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- A bounded analytic source map has bounded chosen stable-infinity cofiber. -/
theorem sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
      .cofiberDegreewiseIsoClosureBoundedMorphisms
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) :=
  TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
    .stableInfinityCofiberTriangle_obj₃_mem_isoClosure_degreewiseIsoClosureBoundedStableObject
      hom

/-- A bounded analytic source map has bounded chosen stable-infinity fiber. -/
theorem sourceStableWeightBoundedMap_mem_fiberDegreewiseIsoClosureBoundedMorphisms
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
      .fiberDegreewiseIsoClosureBoundedMorphisms
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) :=
  TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
    .stableInfinityFiberTriangle_obj₁_degreewiseIsoClosureBoundedStableObject
      hom

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
