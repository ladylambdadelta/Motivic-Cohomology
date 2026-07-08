import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.PretriangulatedFields.Cocone.BoundedSource.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.PretriangulatedFields.Completion.Owner

/-!
# Completion field for bounded analytic source maps

This file removes the explicit cofiber-bounded witnesses from the completion
field for commutative squares of bounded analytic source maps.  The witnesses
are supplied by the stable-infinity bounded-morphism owner theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A commutative square of bounded analytic source maps extends to a morphism
between the chosen degreewise-bounded cofiber triangles. -/
theorem complete_cofiber_triangle_morphism_of_sourceWeightBoundedMap
    {bound : Nat}
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (morphism₁ :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source₁
        target₁)
    (morphism₂ :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source₂
        target₂)
    (sourceMap :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .sourceWeightBoundedObject source₁ ⟶
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .sourceWeightBoundedObject source₂)
    (targetMap :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .sourceWeightBoundedObject target₁ ⟶
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .sourceWeightBoundedObject target₂)
    (square :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .sourceWeightBoundedMap morphism₁ ≫ targetMap =
        sourceMap ≫
          TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .sourceWeightBoundedMap morphism₂) :
    ∃ comparison :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberObject
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .sourceWeightBoundedMap morphism₁)
          (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
            .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
              morphism₁) ⟶
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberObject
            (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .sourceWeightBoundedMap morphism₂)
            (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
              .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
                morphism₂),
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .sourceWeightBoundedMap morphism₁)
          (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
            .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
              morphism₁)).mor₂ ≫ comparison =
        targetMap ≫
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .cofiberTriangle
              (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .sourceWeightBoundedMap morphism₂)
              (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
                .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
                  morphism₂)).mor₂ ∧
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .sourceWeightBoundedMap morphism₁)
          (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
            .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
              morphism₁)).mor₃ ≫ sourceMap⟦(1 : ℤ)⟧' =
        comparison ≫
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .cofiberTriangle
              (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .sourceWeightBoundedMap morphism₂)
              (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
                .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
                  morphism₂)).mor₃ :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .complete_cofiber_triangle_morphism_of_cofiberBounded
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .sourceWeightBoundedMap morphism₁)
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .sourceWeightBoundedMap morphism₂)
      sourceMap
      targetMap
      square
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
          morphism₁)
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
          morphism₂)

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
