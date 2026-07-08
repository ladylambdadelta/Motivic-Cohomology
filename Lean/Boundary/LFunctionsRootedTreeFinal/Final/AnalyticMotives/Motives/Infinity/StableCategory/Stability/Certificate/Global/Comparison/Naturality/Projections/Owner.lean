import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Comparison.Naturality.Owner

/-!
# Projections from the global comparison naturality certificate

This file exposes the four naturality laws bundled by the global comparison
naturality certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Cofiber short-complex naturality at the first structure map. -/
theorem
    traceAnalyticStableInfinityCategory_global_comparison_cofiber_π₁Toπ₂_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (traceAnalyticStableInfinityCategory
            .cofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (traceAnalyticStableInfinityCategory
            .cofiberShortComplex morphism₁) ≫
        targetMap :=
  (traceAnalyticStableInfinityCategory_global_comparison_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).left

/-- Cofiber short-complex naturality at the second structure map. -/
theorem
    traceAnalyticStableInfinityCategory_global_comparison_cofiber_π₂Toπ₃_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (traceAnalyticStableInfinityCategory
            .cofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (traceAnalyticStableInfinityCategory
            .cofiberShortComplex morphism₁) ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  (traceAnalyticStableInfinityCategory_global_comparison_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).right.left

/-- Fiber short-complex naturality at the first structure map. -/
theorem
    traceAnalyticStableInfinityCategory_global_comparison_fiber_π₁Toπ₂_naturality
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
        (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (traceAnalyticStableInfinityCategory
            .fiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (traceAnalyticStableInfinityCategory
            .fiberShortComplex morphism₁) ≫
        sourceMap :=
  (traceAnalyticStableInfinityCategory_global_comparison_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).right.right.left

/-- Fiber short-complex naturality at the second structure map. -/
theorem
    traceAnalyticStableInfinityCategory_global_comparison_fiber_π₂Toπ₃_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (traceAnalyticStableInfinityCategory
            .fiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (traceAnalyticStableInfinityCategory
            .fiberShortComplex morphism₁) ≫
        targetMap :=
  (traceAnalyticStableInfinityCategory_global_comparison_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).right.right.right

end AnalyticMotives
end LFunctions
end Boundary
