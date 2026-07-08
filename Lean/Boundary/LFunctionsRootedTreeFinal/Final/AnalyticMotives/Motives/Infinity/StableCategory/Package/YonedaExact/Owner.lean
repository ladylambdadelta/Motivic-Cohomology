import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level Yoneda exactness for analytic stable motives

This owner file exposes Yoneda exactness through the assembled
`traceAnalyticStableInfinityCategory` package without lengthening the main
stable-category owner file.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The assembled stable-infinity package inherits covariant preadditive
Yoneda exactness for distinguished analytic stable triangles. -/
theorem traceAnalyticStableInfinityCategory_coyonedaShortComplex_exact
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .shortComplexOfDistinguishedTriangle triangle distinguished).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .coyonedaShortComplex_exact triangle distinguished probe

/-- The assembled stable-infinity package inherits contravariant preadditive
Yoneda exactness for distinguished analytic stable triangles. -/
theorem traceAnalyticStableInfinityCategory_yonedaShortComplex_exact
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .shortComplexOfDistinguishedTriangle triangle distinguished).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .yonedaShortComplex_exact triangle distinguished probe

/-- The assembled stable-infinity package inherits covariant preadditive
Yoneda exactness for chosen cofiber short complexes. -/
theorem traceAnalyticStableInfinityCategory_cofiberCoyonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .cofiberCoyonedaShortComplex_exact morphism probe

/-- The assembled stable-infinity package inherits contravariant preadditive
Yoneda exactness for chosen cofiber short complexes. -/
theorem traceAnalyticStableInfinityCategory_cofiberYonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .cofiberYonedaShortComplex_exact morphism probe

/-- The assembled stable-infinity package inherits covariant preadditive
Yoneda exactness for rotated chosen cofiber short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberCoyonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .rotatedCofiberCoyonedaShortComplex_exact morphism probe

/-- The assembled stable-infinity package inherits contravariant preadditive
Yoneda exactness for rotated chosen cofiber short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberYonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .rotatedCofiberYonedaShortComplex_exact morphism probe

/-- The assembled stable-infinity package inherits covariant preadditive
Yoneda exactness for inverse-rotated chosen cofiber short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberCoyonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .invRotatedCofiberCoyonedaShortComplex_exact morphism probe

/-- The assembled stable-infinity package inherits contravariant preadditive
Yoneda exactness for inverse-rotated chosen cofiber short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberYonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .invRotatedCofiberYonedaShortComplex_exact morphism probe

end AnalyticMotives
end LFunctions
end Boundary
