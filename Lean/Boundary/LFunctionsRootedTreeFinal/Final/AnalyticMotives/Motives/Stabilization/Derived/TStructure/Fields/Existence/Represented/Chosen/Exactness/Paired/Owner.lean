import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Exactness.Owner

/-!
# Paired Yoneda exactness for chosen represented truncation triangles

This file bundles the covariant and contravariant exactness of the canonical
distinguished short complex attached to a concrete Yoneda truncation
representative.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

namespace YonedaTruncationRepresentative

/-- Paired covariant and contravariant preadditive Yoneda exactness for the
canonical distinguished truncation short complex. -/
theorem distinguishedShortComplex_yonedaExact_pair
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    (representative.distinguishedShortComplex.map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      (representative.distinguishedShortComplex.op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  And.intro
    (representative.coyonedaDistinguishedShortComplex_exact leftProbe)
    (representative.yonedaDistinguishedShortComplex_exact rightProbe)

/-- Paired covariant and contravariant preadditive Yoneda exactness for the
normalized adjacent cut-`1` canonical distinguished truncation short complex.
-/
theorem normalized_distinguishedShortComplex_yonedaExact_pair
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    (representative.distinguishedShortComplex.map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      (representative.distinguishedShortComplex.op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  representative.distinguishedShortComplex_yonedaExact_pair
    leftProbe
    rightProbe

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
