import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Rotations.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.Comparison.Projections.Naturality.Owner

/-!
# Naturality for rotated cofiber short-complex comparisons

This file exposes the two projection-naturality squares for both rotated and
inverse-rotated cofiber short-complex comparison morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- Naturality of `ShortComplex.π₁Toπ₂` at the rotated cofiber
short-complex comparison. -/
theorem
    stableInfinityRotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityRotatedCofiberShortComplex morphism₁) ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square :=
  traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- Naturality of `ShortComplex.π₂Toπ₃` at the rotated cofiber
short-complex comparison. -/
theorem
    stableInfinityRotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityRotatedCofiberShortComplex morphism₁) ≫
        sourceMap⟦(1 : ℤ)⟧' :=
  traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- Naturality of `ShortComplex.π₁Toπ₂` at the inverse-rotated cofiber
short-complex comparison. -/
theorem
    stableInfinityInvRotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧' ≫
        (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityInvRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityInvRotatedCofiberShortComplex morphism₁) ≫
        sourceMap :=
  traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- Naturality of `ShortComplex.π₂Toπ₃` at the inverse-rotated cofiber
short-complex comparison. -/
theorem
    stableInfinityInvRotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityInvRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityInvRotatedCofiberShortComplex morphism₁) ≫
        targetMap :=
  traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
