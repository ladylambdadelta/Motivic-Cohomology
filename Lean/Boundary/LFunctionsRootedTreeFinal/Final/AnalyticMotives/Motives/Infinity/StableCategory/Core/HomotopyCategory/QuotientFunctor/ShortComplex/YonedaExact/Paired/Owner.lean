import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.ShortComplex.YonedaExact.Owner

/-!
# Paired Yoneda exactness for homotopy quotient short complexes

This file bundles covariant and contravariant preadditive Yoneda exactness for
the short complex attached to a homotopy quotient image.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- Paired preadditive Yoneda exactness for the short complex attached to the
homotopy quotient image of an additive distinguished triangle. -/
theorem homotopyQuotientFunctor_pairedYonedaShortComplex_exact
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      ((TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctor_shortComplex
          triangle
          distinguished).op.map
          (preadditiveYoneda.obj rightProbe)).Exact :=
  And.intro
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_coyonedaShortComplex_exact
        triangle
        distinguished
        leftProbe)
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_yonedaShortComplex_exact
        triangle
        distinguished
        rightProbe)

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
