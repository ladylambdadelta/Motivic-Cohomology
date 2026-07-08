import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Stable.Owner

/-!
# Bounded stable membership for mapping-cone vertices

This file records the bounded stable comparison-source membership of the
source and target vertices in a bounded analytic mapping-cone triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotiveComparison
namespace SourceBoundedMappingCone

/-- The first stable vertex of a bounded analytic mapping-cone triangle is a
bounded stable comparison-source object. -/
theorem stableFirstObject_boundedStableObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableFirstObject hom) :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (Eq.symm
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableFirstObject_eq hom))
    (TraceAnalyticDMgmComparisonSource
      .boundedStableObject_of_sourceStableWeightBoundedObject
        source)

/-- The second stable vertex of a bounded analytic mapping-cone triangle is a
bounded stable comparison-source object. -/
theorem stableSecondObject_boundedStableObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableSecondObject hom) :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (Eq.symm
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableSecondObject_eq hom))
    (TraceAnalyticDMgmComparisonSource
      .boundedStableObject_of_sourceStableWeightBoundedObject
        target)

end SourceBoundedMappingCone
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
