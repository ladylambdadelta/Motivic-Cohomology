import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Associativity.Owner

/-!
# Diagonals of analytic stable motive simplices

This owner file identifies the simplicial diagonal map with the long edge of
concrete analytic stable motive simplices.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The diagonal one-simplex of an analytic stable motive two-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.twoSimplexDiagonal
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  TraceAnalyticStableMotiveQuasicategory.diagonal simplex

/-- The diagonal of a two-simplex is its composite edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.twoSimplexDiagonal_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory
        .twoSimplexDiagonal simplex =
      ComposableArrows.mk₁
        (TraceAnalyticStableMotiveQuasicategory
          .twoSimplexCompositeEdge simplex) :=
  rfl

/-- The diagonal one-simplex of an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexDiagonal
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  TraceAnalyticStableMotiveQuasicategory.diagonal simplex

/-- The diagonal of a three-simplex is its total edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexDiagonal_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexDiagonal simplex =
      ComposableArrows.mk₁
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexTotalEdge simplex) :=
  rfl

/-- The edge of the two-simplex diagonal is the two-simplex composite edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.twoSimplexDiagonal_edge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    (TraceAnalyticStableMotiveQuasicategory
      .twoSimplexDiagonal simplex).map' 0 1 =
      TraceAnalyticStableMotiveQuasicategory
        .twoSimplexCompositeEdge simplex :=
  rfl

/-- The edge of the three-simplex diagonal is the three-simplex total edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexDiagonal_edge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    (TraceAnalyticStableMotiveQuasicategory
      .threeSimplexDiagonal simplex).map' 0 1 =
      TraceAnalyticStableMotiveQuasicategory
        .threeSimplexTotalEdge simplex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
