import Mathlib.CategoryTheory.Triangulated.Yoneda
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.ShortComplex.Owner

/-!
# Yoneda exactness for homotopy quotient short complexes

This file proves the covariant and contravariant preadditive Yoneda exactness
of the short complex attached to the homotopy quotient image of an additive
distinguished triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- Covariant preadditive Yoneda exactness for the short complex attached to
the homotopy quotient image of an additive distinguished triangle. -/
theorem homotopyQuotientFunctor_coyonedaShortComplex_exact
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
  (preadditiveCoyoneda.obj probe).map_distinguished_exact
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
      .mapTriangle.obj triangle)
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_map_distinguished triangle distinguished)

/-- Contravariant preadditive Yoneda exactness for the short complex attached
to the homotopy quotient image of an additive distinguished triangle. -/
theorem homotopyQuotientFunctor_yonedaShortComplex_exact
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
  Pretriangulated.preadditiveYoneda_map_distinguished
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
      .mapTriangle.obj triangle)
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_map_distinguished triangle distinguished)
    probe

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
