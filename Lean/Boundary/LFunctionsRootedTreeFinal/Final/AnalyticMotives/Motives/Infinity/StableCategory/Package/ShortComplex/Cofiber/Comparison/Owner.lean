import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Cofiber.Comparison.Owner

/-!
# Package-level cofiber-comparison morphisms of short complexes

This owner file exposes through `traceAnalyticStableInfinityCategory` the
short-complex morphism induced by a commutative square between morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level morphism between chosen cofiber short complexes induced
by a commutative square between morphisms. -/
def traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberShortComplex morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberShortComplex morphism₂ :=
  traceAnalyticStableInfinityCategory
    .cofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The first component of the package-level cofiber short-complex comparison
is the source map of the original commutative square. -/
theorem traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₁ =
      sourceMap :=
  rfl

/-- The second component of the package-level cofiber short-complex comparison
is the target map of the original commutative square. -/
theorem traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₂ =
      targetMap :=
  rfl

/-- The third component of the package-level cofiber short-complex comparison
is the chosen package-level cofiber comparison map. -/
theorem traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₃ =
      traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The first square of the package-level cofiber short-complex comparison is
the original commutative square, in short-complex orientation. -/
theorem
    traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_comm₁₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (traceAnalyticStableInfinityCategory
          .cofiberShortComplex morphism₂).f =
      (traceAnalyticStableInfinityCategory
        .cofiberShortComplex morphism₁).f ≫
        targetMap :=
  (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁₂

/-- The second square of the package-level cofiber short-complex comparison is
the cocone compatibility square, in short-complex orientation. -/
theorem
    traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (traceAnalyticStableInfinityCategory
          .cofiberShortComplex morphism₂).g =
      (traceAnalyticStableInfinityCategory
        .cofiberShortComplex morphism₁).g ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂₃

end AnalyticMotives
end LFunctions
end Boundary
