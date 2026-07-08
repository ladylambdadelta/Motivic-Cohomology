import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Rotation.Squares.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.CofiberRotations.Comparison.Owner

/-!
# Package-level comparison morphisms for rotated cofiber short complexes

This owner file exposes through `traceAnalyticStableInfinityCategory` the
rotated and inverse-rotated cofiber comparison morphisms as morphisms between
the corresponding rotated cofiber short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level morphism between rotated cofiber short complexes induced
by a commutative square. -/
def traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
        morphism₁ ⟶
      traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
        morphism₂ :=
  traceAnalyticStableInfinityCategory
    .rotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The package-level morphism between inverse-rotated cofiber short complexes
induced by a commutative square. -/
def traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.invRotatedCofiberShortComplex
        morphism₁ ⟶
      traceAnalyticStableInfinityCategory.invRotatedCofiberShortComplex
        morphism₂ :=
  traceAnalyticStableInfinityCategory
    .invRotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The first component of the package-level rotated cofiber short-complex
comparison is the target map. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₁ =
      targetMap :=
  rfl

/-- The second component of the package-level rotated cofiber short-complex
comparison is the induced cofiber comparison map. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₂ =
      traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The third component of the package-level rotated cofiber short-complex
comparison is the shifted source map. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₃ =
      sourceMap⟦(1 : ℤ)⟧' :=
  rfl

/-- The first component of the package-level inverse-rotated cofiber
short-complex comparison is the shifted cofiber comparison map. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
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

/-- The second component of the package-level inverse-rotated cofiber
short-complex comparison is the source map. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₂ =
      sourceMap :=
  rfl

/-- The third component of the package-level inverse-rotated cofiber
short-complex comparison is the target map. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₃ =
      targetMap :=
  rfl

/-- The first square of the package-level rotated cofiber short-complex
comparison. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_comm₁₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (traceAnalyticStableInfinityCategory
          .rotatedCofiberShortComplex morphism₂).f =
      (traceAnalyticStableInfinityCategory
        .rotatedCofiberShortComplex morphism₁).f ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁₂

/-- The second square of the package-level rotated cofiber short-complex
comparison. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        (traceAnalyticStableInfinityCategory
          .rotatedCofiberShortComplex morphism₂).g =
      (traceAnalyticStableInfinityCategory
        .rotatedCofiberShortComplex morphism₁).g ≫
        sourceMap⟦(1 : ℤ)⟧' :=
  (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂₃

/-- The first square of the package-level inverse-rotated cofiber
short-complex comparison. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_comm₁₂
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
        (traceAnalyticStableInfinityCategory
          .invRotatedCofiberShortComplex morphism₂).f =
      (traceAnalyticStableInfinityCategory
        .invRotatedCofiberShortComplex morphism₁).f ≫
        sourceMap :=
  (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁₂

/-- The second square of the package-level inverse-rotated cofiber
short-complex comparison. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (traceAnalyticStableInfinityCategory
          .invRotatedCofiberShortComplex morphism₂).g =
      (traceAnalyticStableInfinityCategory
        .invRotatedCofiberShortComplex morphism₁).g ≫
        targetMap :=
  (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂₃

end AnalyticMotives
end LFunctions
end Boundary
