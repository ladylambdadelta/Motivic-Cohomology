import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.ShortComplex.YonedaExact.Owner

/-!
# Projections for quotient-image Yoneda exactness

This file exposes projection names for covariant and contravariant
preadditive Yoneda exactness of the short complex attached to a homotopy
quotient image.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- Projection form of covariant preadditive Yoneda exactness for the
homotopy quotient image short complex. -/
theorem homotopyQuotientFunctor_coyoneda_exact
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (probe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ) :
    ((TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_coyonedaShortComplex_exact
      triangle
      distinguished
      probe

/-- Projection form of contravariant preadditive Yoneda exactness for the
homotopy quotient image short complex. -/
theorem homotopyQuotientFunctor_yoneda_exact
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (probe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    ((TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_yonedaShortComplex_exact
      triangle
      distinguished
      probe

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
