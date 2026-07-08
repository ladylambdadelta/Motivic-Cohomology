import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Stability certificate for analytic stable motives

This file states the stable-infinity-category theorem surface directly from
the constructed owner object.  It does not add assumptions: every declaration
below is a projection from `traceAnalyticStableInfinityCategory`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The analytic stable motive object is a quasicategory. -/
def traceAnalyticStableInfinityCategory_isQuasicategory :
    Quasicategory TraceAnalyticStableMotiveQuasicategory :=
  traceAnalyticStableInfinityCategory.quasicategory

/-- The presented analytic stable motive category is pointed. -/
def traceAnalyticStableInfinityCategory_isPointed :
    HasZeroObject StableInfinityOwner.PresentedCategory :=
  traceAnalyticStableInfinityCategory.zeroObject

/-- The presented analytic stable motive category has integer shifts. -/
def traceAnalyticStableInfinityCategory_hasShift :
    HasShift StableInfinityOwner.PresentedCategory ℤ :=
  traceAnalyticStableInfinityCategory.shift

/-- Suspension in analytic stable motives is the positive unit shift. -/
def traceAnalyticStableInfinityCategory_suspensionFunctor :
    StableInfinityOwner.PresentedCategory ⥤
      StableInfinityOwner.PresentedCategory :=
  traceAnalyticStableInfinityCategory.suspension

/-- Loop in analytic stable motives is the negative unit shift. -/
def traceAnalyticStableInfinityCategory_loopFunctor :
    StableInfinityOwner.PresentedCategory ⥤
      StableInfinityOwner.PresentedCategory :=
  traceAnalyticStableInfinityCategory.loop

/-- Suspension and loop are inverse through the unit shift equivalence. -/
def traceAnalyticStableInfinityCategory_suspensionLoopEquivalence_owner :
    StableInfinityOwner.PresentedCategory ≌
      StableInfinityOwner.PresentedCategory :=
  traceAnalyticStableInfinityCategory.suspensionLoopEquivalence

/-- The analytic stable motive category is triangulated. -/
def traceAnalyticStableInfinityCategory_isTriangulated :
    IsTriangulated StableInfinityOwner.PresentedCategory :=
  traceAnalyticStableInfinityCategory.triangulated

/-- Every morphism has the owner-level distinguished cofiber triangle. -/
def traceAnalyticStableInfinityCategory_cofiberTriangleFor
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedTriangle :=
  traceAnalyticStableInfinityCategory.cofiberTriangle morphism

/-- Every owner-level cofiber triangle is distinguished. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangleFor_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_cofiberTriangleFor morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory.cofiberTriangle_distinguished morphism

/-- Every morphism has the owner-level distinguished fiber triangle. -/
def traceAnalyticStableInfinityCategory_fiberTriangleFor
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedTriangle :=
  traceAnalyticStableInfinityCategory.fiberTriangle morphism

/-- Every owner-level fiber triangle is distinguished. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangleFor_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberTriangleFor morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory.fiberTriangle_distinguished morphism

/-- Owner-level fiber triangles are inverse rotations of cofiber triangles. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangleFor_eq_invRotate
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberTriangleFor morphism =
      (traceAnalyticStableInfinityCategory_cofiberTriangleFor
        morphism).invRotate :=
  traceAnalyticStableInfinityCategory.fiberTriangle_eq_invRotate_cofiber
    morphism

/-- Distinguished analytic stable triangles are exact after covariant
preadditive Yoneda evaluation. -/
theorem traceAnalyticStableInfinityCategory_distinguished_coyoneda_exact
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .shortComplexOfDistinguishedTriangle
        triangle
        distinguished).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory.coyonedaShortComplex_exact
    triangle
    distinguished
    probe

/-- Distinguished analytic stable triangles are exact after contravariant
preadditive Yoneda evaluation. -/
theorem traceAnalyticStableInfinityCategory_distinguished_yoneda_exact
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .shortComplexOfDistinguishedTriangle
        triangle
        distinguished).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory.yonedaShortComplex_exact
    triangle
    distinguished
    probe

/-- Cofiber short complexes are exact after covariant preadditive Yoneda
evaluation. -/
theorem traceAnalyticStableInfinityCategory_cofiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .cofiberCoyonedaShortComplex_exact morphism probe

/-- Cofiber short complexes are exact after contravariant preadditive Yoneda
evaluation. -/
theorem traceAnalyticStableInfinityCategory_cofiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .cofiberYonedaShortComplex_exact morphism probe

/-- Fiber short complexes are exact after covariant preadditive Yoneda
evaluation. -/
theorem traceAnalyticStableInfinityCategory_fiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .fiberCoyonedaShortComplex_exact morphism probe

/-- Fiber short complexes are exact after contravariant preadditive Yoneda
evaluation. -/
theorem traceAnalyticStableInfinityCategory_fiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .fiberYonedaShortComplex_exact morphism probe

/-- In every distinguished analytic stable triangle, the first two maps
compose to zero. -/
theorem traceAnalyticStableInfinityCategory_distinguished_mor₁_comp_mor₂
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₁ ≫ triangle.mor₂ = 0 :=
  traceAnalyticStableInfinityCategory
    .distinguishedTriangle_mor₁_comp_mor₂
    triangle
    distinguished

/-- In every distinguished analytic stable triangle, the second and third maps
compose to zero. -/
theorem traceAnalyticStableInfinityCategory_distinguished_mor₂_comp_mor₃
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₂ ≫ triangle.mor₃ = 0 :=
  traceAnalyticStableInfinityCategory
    .distinguishedTriangle_mor₂_comp_mor₃
    triangle
    distinguished

/-- In every distinguished analytic stable triangle, the third map followed
by the shifted first map is zero. -/
theorem traceAnalyticStableInfinityCategory_distinguished_mor₃_comp_shift_mor₁
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₃ ≫ triangle.mor₁⟦(1 : ℤ)⟧' = 0 :=
  traceAnalyticStableInfinityCategory
    .distinguishedTriangle_mor₃_comp_shift_mor₁
    triangle
    distinguished

/-- For the chosen cofiber triangle, the original morphism followed by the
chosen cocone map is zero. -/
theorem traceAnalyticStableInfinityCategory_cofiber_morphism_comp_cocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    morphism ≫
        traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism =
      0 :=
  traceAnalyticStableInfinityCategory
    .cofiber_morphism_comp_cocone morphism

/-- For the chosen cofiber triangle, the chosen cocone map followed by the
chosen boundary map is zero. -/
theorem traceAnalyticStableInfinityCategory_cofiber_cocone_comp_boundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism ≫
        traceAnalyticStableInfinityCategory.cofiberBoundary morphism =
      0 :=
  traceAnalyticStableInfinityCategory
    .cofiber_cocone_comp_boundary morphism

/-- For the chosen cofiber triangle, the chosen boundary map followed by the
shifted original morphism is zero. -/
theorem traceAnalyticStableInfinityCategory_cofiber_boundary_comp_shift_morphism
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism ≫
        morphism⟦(1 : ℤ)⟧' =
      0 :=
  traceAnalyticStableInfinityCategory
    .cofiber_boundary_comp_shift_morphism morphism

/-- For the chosen fiber triangle, the chosen fiber map followed by the
original morphism is zero. -/
theorem traceAnalyticStableInfinityCategory_fiberMap_comp_morphism
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.fiberMap morphism ≫ morphism = 0 :=
  traceAnalyticStableInfinityCategory
    .fiberMap_comp_morphism morphism

/-- A commutative square of morphisms induces a map between the chosen
cofibers in analytic stable motives. -/
def traceAnalyticStableInfinityCategory_cofiberComparisonMapFor
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberObject morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberObject morphism₂ :=
  traceAnalyticStableInfinityCategory
    .cofiberComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The induced cofiber comparison map is compatible with the chosen cocone
maps. -/
theorem traceAnalyticStableInfinityCategory_cofiberComparisonMapFor_cocone
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism₁ ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMapFor
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism₂ :=
  traceAnalyticStableInfinityCategory
    .cofiberComparisonMap_cocone
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The induced cofiber comparison map is compatible with the chosen boundary
maps. -/
theorem traceAnalyticStableInfinityCategory_cofiberComparisonMapFor_boundary
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism₁ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      traceAnalyticStableInfinityCategory_cofiberComparisonMapFor
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        traceAnalyticStableInfinityCategory.cofiberBoundary morphism₂ :=
  traceAnalyticStableInfinityCategory
    .cofiberComparisonMap_boundary
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- A commutative square of morphisms induces a morphism of the chosen
cofiber triangles. -/
def traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMapFor
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberTriangle morphism₂ :=
  traceAnalyticStableInfinityCategory
    .cofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- A commutative square of morphisms induces a morphism of the chosen
rotated cofiber triangles. -/
def traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMapFor
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism₂ :=
  traceAnalyticStableInfinityCategory
    .rotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- A commutative square of morphisms induces a morphism of the chosen
inverse-rotated cofiber triangles. -/
def
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMapFor
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
        morphism₂ :=
  traceAnalyticStableInfinityCategory
    .invRotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- A commutative square of morphisms induces a morphism of the chosen fiber
triangles. -/
def traceAnalyticStableInfinityCategory_fiberTriangleComparisonMapFor
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.fiberTriangle morphism₂ :=
  traceAnalyticStableInfinityCategory
    .fiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- A commutative square of morphisms induces a morphism of the chosen
cofiber short complexes. -/
def traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMapFor
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

/-- A commutative square of morphisms induces a morphism of the chosen fiber
short complexes. -/
def traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMapFor
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.fiberShortComplex morphism₁ ⟶
      traceAnalyticStableInfinityCategory.fiberShortComplex morphism₂ :=
  traceAnalyticStableInfinityCategory
    .fiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- Binary biproduct short complexes are exact after covariant preadditive
Yoneda evaluation. -/
theorem traceAnalyticStableInfinityCategory_binaryBiproduct_coyoneda_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .binaryBiproductShortComplex left right).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductCoyonedaShortComplex_exact left right probe

/-- Binary biproduct short complexes are exact after contravariant
preadditive Yoneda evaluation. -/
theorem traceAnalyticStableInfinityCategory_binaryBiproduct_yoneda_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .binaryBiproductShortComplex left right).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductYonedaShortComplex_exact left right probe

end AnalyticMotives
end LFunctions
end Boundary
