import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Owner

/-!
# Zero-composition laws for analytic stable motive triangles

This owner file records the zero-composition laws carried by distinguished
analytic stable triangles, and specializes them to the chosen cofiber triangle
of each morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first two maps of a distinguished analytic stable triangle compose to
zero. -/
theorem TraceAnalyticStableMotiveQuasicategory.distinguishedTriangle_mor₁_comp_mor₂
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    triangle.mor₁ ≫ triangle.mor₂ = 0 :=
  Pretriangulated.comp_distTriang_mor_zero₁₂ triangle distinguished

/-- The second and third maps of a distinguished analytic stable triangle
compose to zero. -/
theorem TraceAnalyticStableMotiveQuasicategory.distinguishedTriangle_mor₂_comp_mor₃
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    triangle.mor₂ ≫ triangle.mor₃ = 0 :=
  Pretriangulated.comp_distTriang_mor_zero₂₃ triangle distinguished

/-- The third map followed by the shifted first map of a distinguished
analytic stable triangle is zero. -/
theorem TraceAnalyticStableMotiveQuasicategory.distinguishedTriangle_mor₃_comp_shift_mor₁
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    triangle.mor₃ ≫ triangle.mor₁⟦(1 : ℤ)⟧' = 0 :=
  Pretriangulated.comp_distTriang_mor_zero₃₁ triangle distinguished

/-- The zero field of the short complex attached to a distinguished triangle
is the first distinguished-triangle zero-composition law. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.shortComplexOfDistinguishedTriangle_zero
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    (TraceAnalyticStableMotiveQuasicategory
      .shortComplexOfDistinguishedTriangle
        triangle
        distinguished).zero =
      TraceAnalyticStableMotiveQuasicategory
        .distinguishedTriangle_mor₁_comp_mor₂ triangle distinguished :=
  rfl

/-- In the chosen cofiber triangle of a morphism, the original morphism
followed by the chosen cocone map is zero. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiber_morphism_comp_cocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    morphism ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap morphism =
      0 :=
  TraceAnalyticStableMotiveQuasicategory
    .distinguishedTriangle_mor₁_comp_mor₂
      (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberTriangle_distinguished morphism)

/-- In the chosen cofiber triangle of a morphism, the chosen cocone map
followed by the chosen boundary map is zero. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiber_cocone_comp_boundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap morphism ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberBoundary morphism =
      0 :=
  TraceAnalyticStableMotiveQuasicategory
    .distinguishedTriangle_mor₂_comp_mor₃
      (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberTriangle_distinguished morphism)

/-- In the chosen cofiber triangle of a morphism, the chosen boundary map
followed by the shifted original morphism is zero. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiber_boundary_comp_shift_morphism
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.cofiberBoundary morphism ≫
        morphism⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticStableMotiveQuasicategory
    .distinguishedTriangle_mor₃_comp_shift_mor₁
      (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberTriangle_distinguished morphism)

/-- The zero field of the chosen cofiber short complex is the concrete
cofiber zero-composition law. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberShortComplex_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplex morphism).zero =
      TraceAnalyticStableMotiveQuasicategory
        .cofiber_morphism_comp_cocone morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
