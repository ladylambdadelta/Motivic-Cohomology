import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Bounded.MappingCone.VertexIso.Owner

/-!
# First square for chosen cofibers and bounded mapping cones

This file proves the commutative first square needed to identify the chosen
stable-infinity cofiber triangle of a bounded source map with the concrete
stable mapping-cone triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotiveComparison
namespace SourceComplexWeightBoundedBy

/-- The first morphism square commutes for the first two vertex isomorphisms
from the chosen stable-infinity cofiber triangle to the concrete stable
bounded mapping-cone triangle. -/
theorem stableInfinityCofiberTriangle_firstSquare_stableMappingConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).mor₁ ≫
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableInfinityCofiberTriangleObj₂IsoStableMappingConeTriangleObj₂
          hom).hom =
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .stableInfinityCofiberTriangleObj₁IsoStableMappingConeTriangleObj₁
          hom).hom ≫
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableTriangle hom).mor₁ := by
  let obj₁_eq :=
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_obj₁_eq_stableMappingConeTriangle_obj₁
        hom
  let obj₂_eq :=
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_obj₂_eq_stableMappingConeTriangle_obj₂
        hom
  let mor₁_eq :=
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
      .stableInfinityCofiberTriangle_mor₁_eq_stableMappingConeTriangle_mor₁
        hom
  change
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).mor₁ ≫
      (eqToIso obj₂_eq).hom =
      (eqToIso obj₁_eq).hom ≫
        (TraceAnalyticMotiveComparison.SourceBoundedMappingCone
          .stableTriangle hom).mor₁
  cases obj₁_eq
  cases obj₂_eq
  exact
    Eq.trans
      (Category.comp_id
        ((TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangle
            (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom)).mor₁))
      (Eq.trans
        mor₁_eq
        (Eq.symm
          (Category.id_comp
            ((TraceAnalyticMotiveComparison.SourceBoundedMappingCone
              .stableTriangle hom).mor₁))))

end SourceComplexWeightBoundedBy
end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
