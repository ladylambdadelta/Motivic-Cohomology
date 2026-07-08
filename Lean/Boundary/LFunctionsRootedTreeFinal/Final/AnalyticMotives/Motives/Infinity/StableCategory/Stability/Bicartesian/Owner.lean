import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Owner

/-!
# Bicartesian stability surface for analytic stable motives

This file records the concrete stability bridge already proved for the
Verdier-localized analytic motive category: the chosen fiber triangle of a
morphism is the inverse rotation of its chosen cofiber triangle, and both
short complexes are exact after the two preadditive Yoneda tests.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The cofiber and fiber triangles attached to one morphism form the same
stable datum: the fiber triangle is the inverse rotation of the cofiber
triangle, and both triangles are distinguished. -/
theorem traceAnalyticStableInfinityCategory_cofiberFiberTriangle_stability
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
      traceAnalyticStableInfinityCategory.fiberTriangle morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
        traceAnalyticStableInfinityCategory.fiberTriangle morphism =
          (traceAnalyticStableInfinityCategory
            .cofiberTriangle morphism).invRotate :=
  And.intro
    (traceAnalyticStableInfinityCategory
      .cofiberTriangle_distinguished morphism)
    (And.intro
      (traceAnalyticStableInfinityCategory
        .fiberTriangle_distinguished morphism)
      (traceAnalyticStableInfinityCategory
        .fiberTriangle_eq_invRotate_cofiber morphism))

/-- The cofiber/fiber object-level duality: the chosen fiber is the negative
unit shift of the chosen cofiber. -/
theorem traceAnalyticStableInfinityCategory_fiberObject_is_desuspended_cofiber
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.fiberObject morphism =
      (traceAnalyticStableInfinityCategory
        .cofiberObject morphism)⟦(-1 : ℤ)⟧ :=
  traceAnalyticStableInfinityCategory
    .fiberObject_eq_cofiber_shift_neg morphism

/-- The cofiber/fiber map-level duality for the map into the source. -/
theorem traceAnalyticStableInfinityCategory_fiberMap_is_desuspended_boundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.fiberMap morphism =
      -((traceAnalyticStableInfinityCategory
        .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  traceAnalyticStableInfinityCategory
    .fiberMap_eq_cofiberBoundary_shift morphism

/-- The cofiber/fiber map-level duality for the connecting map out of the
target. -/
theorem traceAnalyticStableInfinityCategory_fiberConnectingMap_is_cofiberCocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .fiberTriangle morphism).mor₃ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap
          morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  traceAnalyticStableInfinityCategory
    .fiberConnectingMap_eq_cofiberCocone morphism

/-- Cofiber and fiber short complexes attached to one morphism are both exact
under covariant preadditive Yoneda tests. -/
theorem traceAnalyticStableInfinityCategory_cofiberFiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact ∧
      ((traceAnalyticStableInfinityCategory
        .fiberShortComplex morphism).map
          (preadditiveCoyoneda.obj probe)).Exact :=
  And.intro
    (traceAnalyticStableInfinityCategory
      .cofiberCoyonedaShortComplex_exact morphism probe)
    (traceAnalyticStableInfinityCategory
      .fiberCoyonedaShortComplex_exact morphism probe)

/-- Cofiber and fiber short complexes attached to one morphism are both exact
under contravariant preadditive Yoneda tests. -/
theorem traceAnalyticStableInfinityCategory_cofiberFiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact ∧
      ((traceAnalyticStableInfinityCategory
        .fiberShortComplex morphism).op.map
          (preadditiveYoneda.obj probe)).Exact :=
  And.intro
    (traceAnalyticStableInfinityCategory
      .cofiberYonedaShortComplex_exact morphism probe)
    (traceAnalyticStableInfinityCategory
      .fiberYonedaShortComplex_exact morphism probe)

/-- The cofiber and fiber zero-composition laws for one morphism, packaged as
the concrete exact-triangle boundary calculation. -/
theorem traceAnalyticStableInfinityCategory_cofiberFiber_zero_compositions
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    morphism ≫
          traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism =
        0 ∧
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism ≫
          traceAnalyticStableInfinityCategory.cofiberBoundary morphism =
        0 ∧
        traceAnalyticStableInfinityCategory.cofiberBoundary morphism ≫
            morphism⟦(1 : ℤ)⟧' =
          0 ∧
          traceAnalyticStableInfinityCategory.fiberMap morphism ≫
              morphism =
            0 :=
  And.intro
    (traceAnalyticStableInfinityCategory
      .cofiber_morphism_comp_cocone morphism)
    (And.intro
      (traceAnalyticStableInfinityCategory
        .cofiber_cocone_comp_boundary morphism)
      (And.intro
        (traceAnalyticStableInfinityCategory
          .cofiber_boundary_comp_shift_morphism morphism)
        (traceAnalyticStableInfinityCategory
          .fiberMap_comp_morphism morphism)))

end AnalyticMotives
end LFunctions
end Boundary
