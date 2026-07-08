import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.CofiberTriangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Comparison.Owner

/-!
# Cofiber-triangle comparison in the degreewise bounded source

This file lifts the analytic stable-infinity cofiber comparison map to the
degreewise bounded source whenever both chosen cofibers satisfy the
degreewise-bounded closure condition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The comparison map between chosen degreewise-bounded cofiber objects
induced by a commutative square. -/
def cofiberComparisonMap
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
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberObject morphism₁ cofiberBounded₁ ⟶
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberObject morphism₂ cofiberBounded₂ :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCofiberComparisonMap
      (TraceAnalyticDMgmComparisonSource
        .DegreewiseBoundedStable.inclusion.map morphism₁)
      (TraceAnalyticDMgmComparisonSource
        .DegreewiseBoundedStable.inclusion.map morphism₂)
      (TraceAnalyticDMgmComparisonSource
        .DegreewiseBoundedStable.inclusion.map sourceMap)
      (TraceAnalyticDMgmComparisonSource
        .DegreewiseBoundedStable.inclusion.map targetMap)
      square

/-- The chosen degreewise-bounded cofiber triangles are functorial under a
commutative square whose two cofibers stay degreewise bounded. -/
def cofiberTriangleComparisonMap
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
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle morphism₁ cofiberBounded₁ ⟶
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberTriangle morphism₂ cofiberBounded₂ :=
  Pretriangulated.Triangle.homMk
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberTriangle morphism₁ cofiberBounded₁)
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberTriangle morphism₂ cofiberBounded₂)
    sourceMap
    targetMap
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square
        cofiberBounded₁
        cofiberBounded₂)
    square
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberComparisonMap_cocone
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map morphism₁)
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map morphism₂)
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map sourceMap)
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map targetMap)
        square)
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberComparisonMap_boundary
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map morphism₁)
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map morphism₂)
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map sourceMap)
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map targetMap)
        square)

/-- The first component of the degreewise-bounded cofiber-triangle comparison
is the source map of the original square. -/
theorem cofiberTriangleComparisonMap_hom₁
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
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square
        cofiberBounded₁
        cofiberBounded₂).hom₁ =
      sourceMap :=
  rfl

/-- The second component of the degreewise-bounded cofiber-triangle comparison
is the target map of the original square. -/
theorem cofiberTriangleComparisonMap_hom₂
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
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square
        cofiberBounded₁
        cofiberBounded₂).hom₂ =
      targetMap :=
  rfl

/-- The third component of the degreewise-bounded cofiber-triangle comparison
is the lifted analytic stable-infinity cofiber comparison map. -/
theorem cofiberTriangleComparisonMap_hom₃
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
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square
        cofiberBounded₁
        cofiberBounded₂).hom₃ =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square
          cofiberBounded₁
          cofiberBounded₂ :=
  rfl

/-- The first square of the lifted cofiber-triangle comparison is the
original commutative square. -/
theorem cofiberTriangleComparisonMap_comm₁
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
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberTriangle morphism₁ cofiberBounded₁).mor₁ ≫
        targetMap =
      sourceMap ≫
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberTriangle morphism₂ cofiberBounded₂).mor₁ :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
      cofiberBounded₁
      cofiberBounded₂).comm₁

/-- The second square of the lifted cofiber-triangle comparison is the
analytic cocone-compatibility square. -/
theorem cofiberTriangleComparisonMap_comm₂
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
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberTriangle morphism₁ cofiberBounded₁).mor₂ ≫
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square
            cofiberBounded₁
            cofiberBounded₂ =
      targetMap ≫
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberTriangle morphism₂ cofiberBounded₂).mor₂ :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
      cofiberBounded₁
      cofiberBounded₂).comm₂

/-- The third square of the lifted cofiber-triangle comparison is the analytic
boundary-compatibility square. -/
theorem cofiberTriangleComparisonMap_comm₃
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
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberTriangle morphism₁ cofiberBounded₁).mor₃ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square
            cofiberBounded₁
            cofiberBounded₂ ≫
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberTriangle morphism₂ cofiberBounded₂).mor₃ :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
      cofiberBounded₁
      cofiberBounded₂).comm₃

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
