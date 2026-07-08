import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Triangles.MappingCone.Vertices.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Stable.Triangle.Owner

/-!
# Iso-closure bounded vertices of stable mapping-cone triangles

This file attaches the degreewise iso-closure bounded stable-source predicate
to the actual stable distinguished triangle obtained from a bounded analytic
mapping-cone triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotiveComparison
namespace SourceBoundedMappingCone

/-- The first vertex of the stable bounded mapping-cone triangle belongs to
the degreewise iso-closure bounded stable-source predicate. -/
theorem stableTriangle_obj₁_degreewiseIsoClosureBoundedStableObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableTriangle hom).obj₁ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject object)
    (Eq.symm
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle_obj₁ hom))
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableFirstObject_degreewiseIsoClosureBoundedStableObject hom)

/-- The second vertex of the stable bounded mapping-cone triangle belongs to
the degreewise iso-closure bounded stable-source predicate. -/
theorem stableTriangle_obj₂_degreewiseIsoClosureBoundedStableObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableTriangle hom).obj₂ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject object)
    (Eq.symm
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle_obj₂ hom))
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableSecondObject_degreewiseIsoClosureBoundedStableObject hom)

/-- The third vertex of the stable bounded mapping-cone triangle belongs to
the degreewise iso-closure bounded stable-source predicate. -/
theorem stableTriangle_obj₃_degreewiseIsoClosureBoundedStableObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableTriangle hom).obj₃ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject object)
    (Eq.symm
      (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
        .stableTriangle_obj₃ hom))
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
      .stableThirdObject_degreewiseIsoClosureBoundedStableObject hom)

end SourceBoundedMappingCone
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
