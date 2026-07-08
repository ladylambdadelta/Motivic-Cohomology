import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.CofiberTriangle.Comparison.Owner

/-!
# Completion field for degreewise bounded cofiber triangles

This file gives the supported Mathlib `complete_distinguished_triangle_morphism`
field shape for the chosen degreewise-bounded cofiber triangles.  The theorem
is intentionally stated at the cofiber-bounded owner layer, where the analytic
stable-infinity comparison map supplies the third component.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A commutative square between cofiber-bounded maps extends to a morphism
between their chosen degreewise-bounded cofiber triangles. -/
theorem complete_cofiber_triangle_morphism_of_cofiberBounded
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂)
    (cofiberBounded₁ :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism₁))
    (cofiberBounded₂ :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism₂)) :
    ∃ comparison :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberObject morphism₁ cofiberBounded₁ ⟶
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberObject morphism₂ cofiberBounded₂,
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle morphism₁ cofiberBounded₁).mor₂ ≫
          comparison =
        targetMap ≫
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .cofiberTriangle morphism₂ cofiberBounded₂).mor₂ ∧
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle morphism₁ cofiberBounded₁).mor₃ ≫
          sourceMap⟦(1 : ℤ)⟧' =
        comparison ≫
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .cofiberTriangle morphism₂ cofiberBounded₂).mor₃ :=
  Exists.intro
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square
        cofiberBounded₁
        cofiberBounded₂)
    (And.intro
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangleComparisonMap_comm₂
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square
          cofiberBounded₁
          cofiberBounded₂)
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangleComparisonMap_comm₃
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square
          cofiberBounded₁
          cofiberBounded₂))

/-- The Mathlib completion-field statement for two chosen cofiber triangles
with cofiber-bounded vertices. -/
theorem complete_distinguished_triangle_morphism_of_cofiberBounded
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (cofiberBounded₁ :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism₁))
    (cofiberBounded₂ :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism₂))
    (square :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle morphism₁ cofiberBounded₁).mor₁ ≫ targetMap =
        sourceMap ≫
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .cofiberTriangle morphism₂ cofiberBounded₂).mor₁) :
    ∃ comparison :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle morphism₁ cofiberBounded₁).obj₃ ⟶
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberTriangle morphism₂ cofiberBounded₂).obj₃,
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle morphism₁ cofiberBounded₁).mor₂ ≫
          comparison =
        targetMap ≫
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .cofiberTriangle morphism₂ cofiberBounded₂).mor₂ ∧
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle morphism₁ cofiberBounded₁).mor₃ ≫
          sourceMap⟦(1 : ℤ)⟧' =
        comparison ≫
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .cofiberTriangle morphism₂ cofiberBounded₂).mor₃ :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .complete_cofiber_triangle_morphism_of_cofiberBounded
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
      cofiberBounded₁
      cofiberBounded₂

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
