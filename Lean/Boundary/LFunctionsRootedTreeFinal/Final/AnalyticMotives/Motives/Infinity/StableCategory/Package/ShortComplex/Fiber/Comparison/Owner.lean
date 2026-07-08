import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Fiber.Comparison.Owner

/-!
# Package-level fiber-comparison morphisms of short complexes

This owner file exposes through `traceAnalyticStableInfinityCategory` the
short-complex morphism induced by a commutative square between morphisms on the
fiber side.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level morphism between chosen fiber short complexes induced by
a commutative square. -/
def traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory_fiberShortComplex morphism₁ ⟶
      traceAnalyticStableInfinityCategory_fiberShortComplex morphism₂ :=
  traceAnalyticStableInfinityCategory
    .fiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The first component of the package-level fiber short-complex comparison
is the desuspended cofiber comparison map. -/
theorem traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₁ =
      (traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The second component of the package-level fiber short-complex comparison
is the source map of the original commutative square. -/
theorem traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₂ =
      sourceMap :=
  rfl

/-- The third component of the package-level fiber short-complex comparison
is the target map of the original commutative square. -/
theorem traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₃ =
      targetMap :=
  rfl

/-- The first square of the package-level fiber short-complex comparison is
the fiber-map compatibility square. -/
theorem
    traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_comm₁₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧' ≫
        (traceAnalyticStableInfinityCategory_fiberShortComplex
          morphism₂).f =
      (traceAnalyticStableInfinityCategory_fiberShortComplex
        morphism₁).f ≫
        sourceMap :=
  (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁₂

/-- The second square of the package-level fiber short-complex comparison is
the original commutative square. -/
theorem
    traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (traceAnalyticStableInfinityCategory_fiberShortComplex
          morphism₂).g =
      (traceAnalyticStableInfinityCategory_fiberShortComplex
        morphism₁).g ≫
        targetMap :=
  (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂₃

end AnalyticMotives
end LFunctions
end Boundary
