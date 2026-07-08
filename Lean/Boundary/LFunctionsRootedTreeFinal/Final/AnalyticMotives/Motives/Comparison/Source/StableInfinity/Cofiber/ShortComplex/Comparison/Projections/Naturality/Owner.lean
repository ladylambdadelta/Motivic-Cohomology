import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Cofiber.Comparison.Projections.Naturality.Owner

/-!
# Naturality of cofiber short-complex projections in the comparison source

This file records the naturality squares for the two projection morphisms of
the comparison-source cofiber short-complex comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- Naturality of `ShortComplex.π₁Toπ₂` at the comparison-source cofiber
short-complex comparison. -/
theorem stableInfinityCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityCofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityCofiberShortComplex morphism₁) ≫
        targetMap :=
  traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_π₁Toπ₂_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- Naturality of `ShortComplex.π₂Toπ₃` at the comparison-source cofiber
short-complex comparison. -/
theorem stableInfinityCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityCofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex TraceAnalyticDMgmComparisonSource ⥤
              TraceAnalyticDMgmComparisonSource) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticDMgmComparisonSource
            .stableInfinityCofiberShortComplex morphism₁) ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square :=
  traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_π₂Toπ₃_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
