import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.ShortComplex.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Comparison.Projections.Naturality.Owner

/-!
# Naturality of fiber short-complex projections in the comparison source

This file records the naturality squares for the two projection morphisms of
the comparison-source fiber short-complex comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- Naturality of `ShortComplex.π₁Toπ₂` at the comparison-source fiber
short-complex comparison. -/
theorem stableInfinityFiberShortComplexComparisonMap_π₁Toπ₂_naturality
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
            .stableInfinityFiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityFiberShortComplex morphism₁) ≫
        sourceMap :=
  traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_π₁Toπ₂_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- Naturality of `ShortComplex.π₂Toπ₃` at the comparison-source fiber
short-complex comparison. -/
theorem stableInfinityFiberShortComplexComparisonMap_π₂Toπ₃_naturality
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
            .stableInfinityFiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityFiberShortComplex morphism₁) ≫
        targetMap :=
  traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_π₂Toπ₃_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
