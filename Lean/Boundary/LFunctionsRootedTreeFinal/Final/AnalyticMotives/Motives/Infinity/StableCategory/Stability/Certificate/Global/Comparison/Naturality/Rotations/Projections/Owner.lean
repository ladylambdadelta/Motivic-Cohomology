import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Comparison.Naturality.Rotations.Owner

/-!
# Projections from the global rotation-naturality certificate

This file exposes the four naturality laws bundled for rotated and
inverse-rotated cofiber short-complex comparison maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Rotated cofiber short-complex naturality at the first structure map. -/
theorem
    traceAnalyticStableInfinityCategory_global_comparison_rotatedCofiber_π₁Toπ₂_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberShortComplex morphism₁) ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  (traceAnalyticStableInfinityCategory_global_comparison_rotation_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).left

/-- Rotated cofiber short-complex naturality at the second structure map. -/
theorem
    traceAnalyticStableInfinityCategory_global_comparison_rotatedCofiber_π₂Toπ₃_naturality
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
        (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberShortComplex morphism₁) ≫
        sourceMap⟦(1 : ℤ)⟧' :=
  (traceAnalyticStableInfinityCategory_global_comparison_rotation_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).right.left

/-- Inverse-rotated cofiber short-complex naturality at the first structure
map. -/
theorem
    traceAnalyticStableInfinityCategory_global_comparison_invRotatedCofiber_π₁Toπ₂_naturality
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
            .invRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (traceAnalyticStableInfinityCategory
            .invRotatedCofiberShortComplex morphism₁) ≫
        sourceMap :=
  (traceAnalyticStableInfinityCategory_global_comparison_rotation_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).right.right.left

/-- Inverse-rotated cofiber short-complex naturality at the second structure
map. -/
theorem
    traceAnalyticStableInfinityCategory_global_comparison_invRotatedCofiber_π₂Toπ₃_naturality
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
            .invRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (traceAnalyticStableInfinityCategory
            .invRotatedCofiberShortComplex morphism₁) ≫
        targetMap :=
  (traceAnalyticStableInfinityCategory_global_comparison_rotation_naturality
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).right.right.right

end AnalyticMotives
end LFunctions
end Boundary
