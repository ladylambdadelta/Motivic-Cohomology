import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Biproduct.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Owner

/-!
# Yoneda exactness for binary biproduct triangles

This owner file specializes Yoneda exactness to binary biproduct and binary
product short complexes in analytic stable motives.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Covariant preadditive Yoneda exactness for binary biproduct short
complexes. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.binaryBiproductCoyonedaShortComplex_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((TraceAnalyticStableMotiveQuasicategory
      .binaryBiproductShortComplex left right).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .coyonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory
        .binaryBiproductTriangle left right)
      (TraceAnalyticStableMotiveQuasicategory
        .binaryBiproductTriangle_distinguished left right)
      probe

/-- Contravariant preadditive Yoneda exactness for binary biproduct short
complexes. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.binaryBiproductYonedaShortComplex_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticStableMotiveQuasicategory
      .binaryBiproductShortComplex left right).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .yonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory
        .binaryBiproductTriangle left right)
      (TraceAnalyticStableMotiveQuasicategory
        .binaryBiproductTriangle_distinguished left right)
      probe

/-- Covariant preadditive Yoneda exactness for binary product short
complexes. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.binaryProductCoyonedaShortComplex_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((TraceAnalyticStableMotiveQuasicategory
      .binaryProductShortComplex left right).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .coyonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory
        .binaryProductTriangle left right)
      (TraceAnalyticStableMotiveQuasicategory
        .binaryProductTriangle_distinguished left right)
      probe

/-- Contravariant preadditive Yoneda exactness for binary product short
complexes. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.binaryProductYonedaShortComplex_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticStableMotiveQuasicategory
      .binaryProductShortComplex left right).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .yonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory
        .binaryProductTriangle left right)
      (TraceAnalyticStableMotiveQuasicategory
        .binaryProductTriangle_distinguished left right)
      probe

end AnalyticMotives
end LFunctions
end Boundary
