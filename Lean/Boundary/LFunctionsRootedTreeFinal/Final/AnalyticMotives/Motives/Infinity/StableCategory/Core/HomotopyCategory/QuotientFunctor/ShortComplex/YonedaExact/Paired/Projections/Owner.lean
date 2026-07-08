import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.ShortComplex.YonedaExact.Paired.Owner

/-!
# Projections for paired Yoneda exactness

This file exposes the covariant and contravariant projections from paired
preadditive Yoneda exactness of homotopy quotient short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- Covariant projection from paired Yoneda exactness for a homotopy quotient
short complex. -/
theorem homotopyQuotientFunctor_pairedYonedaShortComplex_coyoneda
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
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_pairedYonedaShortComplex_exact
      triangle
      distinguished
      leftProbe
      rightProbe).left

/-- Contravariant projection from paired Yoneda exactness for a homotopy
quotient short complex. -/
theorem homotopyQuotientFunctor_pairedYonedaShortComplex_yoneda
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
        distinguished).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_pairedYonedaShortComplex_exact
      triangle
      distinguished
      leftProbe
      rightProbe).right

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
