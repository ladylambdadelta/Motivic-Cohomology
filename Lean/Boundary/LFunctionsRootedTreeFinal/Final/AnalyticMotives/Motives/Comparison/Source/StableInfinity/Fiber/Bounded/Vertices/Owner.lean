import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Bounded.MappingCone.ThirdVertex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.IsoClosure.Shift.Owner

/-!
# Bounded vertices of chosen fiber triangles

This file records the bounded-control facts for the chosen stable-infinity
fiber triangle attached to a bounded analytic source map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- The chosen stable-infinity fiber triangle attached to a bounded source map
is distinguished. -/
theorem stableInfinityFiberTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ∈
      Pretriangulated.distTriang TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityFiberTriangle_distinguished
      (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)

/-- The first vertex of the chosen stable-infinity fiber triangle of a bounded
source map belongs to the degreewise iso-closure bounded stable source
predicate. -/
theorem stableInfinityFiberTriangle_obj₁_degreewiseIsoClosureBoundedStableObject
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
          .stableInfinityFiberTriangle
            (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₁ :=
  Eq.subst
    (motive := fun triangle =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject triangle.obj₁)
    (Eq.symm
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle_eq_invRotate_cofiber
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)))
    (TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject_shift
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
          .stableInfinityCofiberTriangle_obj₃_mem_isoClosure_degreewiseIsoClosureBoundedStableObject
            hom)
        (-1 : ℤ))

/-- The second vertex of the chosen stable-infinity fiber triangle of a bounded
source map belongs to the degreewise iso-closure bounded stable source
predicate. -/
theorem stableInfinityFiberTriangle_obj₂_degreewiseIsoClosureBoundedStableObject
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
          .stableInfinityFiberTriangle
            (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₂ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject object)
    (Eq.symm
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle_obj₂
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)))
    (TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject_of_sourceStableWeightBoundedObject
        source)

/-- The third vertex of the chosen stable-infinity fiber triangle of a bounded
source map belongs to the degreewise iso-closure bounded stable source
predicate. -/
theorem stableInfinityFiberTriangle_obj₃_degreewiseIsoClosureBoundedStableObject
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
          .stableInfinityFiberTriangle
            (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₃ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject object)
    (Eq.symm
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle_obj₃
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)))
    (TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject_of_sourceStableWeightBoundedObject
        target)

/-- The chosen stable-infinity fiber triangle of a bounded source map is
distinguished and all three vertices are controlled by the bounded stable
analytic source predicate. -/
theorem stableInfinityFiberTriangle_distinguished_with_bounded_vertices
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ∈
      Pretriangulated.distTriang TraceAnalyticDMgmComparisonSource) ∧
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityFiberTriangle
              (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₁ ∧
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityFiberTriangle
              (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₂ ∧
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityFiberTriangle
              (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).obj₃ :=
  And.intro
    (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityFiberTriangle_distinguished hom)
    (And.intro
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableInfinityFiberTriangle_obj₁_degreewiseIsoClosureBoundedStableObject
          hom)
      (And.intro
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
          .stableInfinityFiberTriangle_obj₂_degreewiseIsoClosureBoundedStableObject
            hom)
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
          .stableInfinityFiberTriangle_obj₃_degreewiseIsoClosureBoundedStableObject
            hom)))

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
