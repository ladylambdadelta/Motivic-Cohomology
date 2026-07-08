import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Triangles.MappingCone.Stable.Owner

/-!
# Stable bounded mapping-cone triangles

This file packages the stable comparison-source image of a bounded analytic
mapping-cone triangle as an actual triangle, and proves that it is
distinguished.  The third morphism of a mapped triangle includes the quotient
functor's shift-commuting isomorphism, so raw connecting-map comparison is left
to the comm-shift owner rather than folded into a false definitional statement.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable comparison-source triangle obtained from a bounded analytic
mapping-cone triangle. -/
def TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    Pretriangulated.Triangle TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.quotientFunctor.mapTriangle.obj
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.triangle hom)

/-- The stable bounded mapping-cone triangle is distinguished. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle hom ∈
      Pretriangulated.distTriang TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.quotientFunctor.map_distinguished
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.triangle hom)
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.triangle_distinguished
      hom)

/-- The first vertex of the stable triangle is the stable first object. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle_obj₁
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle
      hom).obj₁ =
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstObject
        hom :=
  rfl

/-- The second vertex of the stable triangle is the stable second object. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle_obj₂
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle
      hom).obj₂ =
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondObject
        hom :=
  rfl

/-- The third vertex of the stable triangle is the stable third object. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle_obj₃
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle
      hom).obj₃ =
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableThirdObject
        hom :=
  rfl

/-- The first morphism of the stable triangle is the stable first map. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle_mor₁
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle
      hom).mor₁ =
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableFirstMap
        hom :=
  rfl

/-- The second morphism of the stable triangle is the stable second map. -/
theorem TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle_mor₂
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableTriangle
      hom).mor₂ =
      TraceAnalyticMotiveComparison.SourceBoundedMappingCone.stableSecondMap
        hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
