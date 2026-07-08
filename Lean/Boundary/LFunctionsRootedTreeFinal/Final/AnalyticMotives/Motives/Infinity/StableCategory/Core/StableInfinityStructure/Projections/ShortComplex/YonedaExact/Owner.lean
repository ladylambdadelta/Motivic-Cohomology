import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.ShortComplex.Owner

/-!
# Per-morphism Yoneda-exactness projections from the actual stable-infinity certificate

This file peels the eight Yoneda-exactness fields for the canonical
per-morphism short complexes out of the actual stable-infinity structure
certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The actual stable-infinity certificate supplies cofiber short-complex
exactness after contravariant preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_cofiber_coyoneda_exact
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_yoneda_exact
    morphism
    leftProbe
    rightProbe).left

/-- The actual stable-infinity certificate supplies cofiber short-complex
exactness after covariant preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_cofiber_yoneda_exact
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.left

/-- The actual stable-infinity certificate supplies fiber short-complex
exactness after contravariant preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_fiber_coyoneda_exact
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.left

/-- The actual stable-infinity certificate supplies fiber short-complex
exactness after covariant preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_fiber_yoneda_exact
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.left

/-- The actual stable-infinity certificate supplies rotated-cofiber
short-complex exactness after contravariant preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_rotatedCofiber_coyoneda_exact
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.right.left

/-- The actual stable-infinity certificate supplies rotated-cofiber
short-complex exactness after covariant preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_rotatedCofiber_yoneda_exact
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.right.right.left

/-- The actual stable-infinity certificate supplies inverse-rotated-cofiber
short-complex exactness after contravariant preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_invRotatedCofiber_coyoneda_exact
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.right.right.right.left

/-- The actual stable-infinity certificate supplies inverse-rotated-cofiber
short-complex exactness after covariant preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_invRotatedCofiber_yoneda_exact
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.right.right.right.right

end AnalyticMotives
end LFunctions
end Boundary
