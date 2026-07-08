import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Stable.Owner

/-!
# Bounded vertices of chosen cofiber triangles

This file records the first two bounded vertices of the chosen stable-infinity
cofiber triangle attached to a bounded analytic source map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- The chosen stable-infinity cofiber triangle attached to a bounded source
map is distinguished. -/
theorem stableInfinityCofiberTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ∈
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCofiberTriangle_distinguished
      (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)

/-- The first vertex of the chosen stable-infinity cofiber triangle attached
to a bounded source map belongs to the degreewise iso-closure bounded stable
source predicate. -/
theorem stableInfinityCofiberTriangle_obj₁_degreewiseIsoClosureBoundedStableObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangle
            (TraceAnalyticMotiveComparison
              .sourceStableWeightBoundedMap hom)).obj₁ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject object)
    (Eq.symm
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle_obj₁
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)))
    (TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject_of_sourceStableWeightBoundedObject
        source)

/-- The second vertex of the chosen stable-infinity cofiber triangle attached
to a bounded source map belongs to the degreewise iso-closure bounded stable
source predicate. -/
theorem stableInfinityCofiberTriangle_obj₂_degreewiseIsoClosureBoundedStableObject
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangle
            (TraceAnalyticMotiveComparison
              .sourceStableWeightBoundedMap hom)).obj₂ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject object)
    (Eq.symm
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle_obj₂
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)))
    (TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject_of_sourceStableWeightBoundedObject
        target)

/-- The chosen stable-infinity cofiber triangle of a bounded source map is a
distinguished triangle whose first two vertices belong to the degreewise
iso-closure bounded stable source predicate. -/
theorem stableInfinityCofiberTriangle_distinguished_with_bounded_first_two
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
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles) ∧
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityCofiberTriangle
              (TraceAnalyticMotiveComparison
                .sourceStableWeightBoundedMap hom)).obj₁ ∧
        TraceAnalyticDMgmComparisonSource
          .degreewiseIsoClosureBoundedStableObject
            (TraceAnalyticDMgmComparisonSource
              .stableInfinityCofiberTriangle
                (TraceAnalyticMotiveComparison
                  .sourceStableWeightBoundedMap hom)).obj₂ :=
  And.intro
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_distinguished hom)
    (And.intro
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableInfinityCofiberTriangle_obj₁_degreewiseIsoClosureBoundedStableObject
          hom)
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableInfinityCofiberTriangle_obj₂_degreewiseIsoClosureBoundedStableObject
          hom))

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
