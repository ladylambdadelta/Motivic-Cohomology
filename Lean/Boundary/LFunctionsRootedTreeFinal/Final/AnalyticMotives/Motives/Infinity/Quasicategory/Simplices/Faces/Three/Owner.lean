import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Associativity.Owner

/-!
# Faces of analytic stable motive three-simplices

This owner file exposes the four two-dimensional faces of a three-simplex in
the analytic stable motive nerve.  Each face is a concrete composable pair in
the stable analytic motive category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The zeroth face of an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceZero
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 2)) :=
  TraceAnalyticStableMotiveQuasicategory.δ (0 : Fin 4) simplex

/-- The first face of an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceOne
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 2)) :=
  TraceAnalyticStableMotiveQuasicategory.δ (1 : Fin 4) simplex

/-- The second face of an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceTwo
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 2)) :=
  TraceAnalyticStableMotiveQuasicategory.δ (2 : Fin 4) simplex

/-- The third face of an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceThree
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 2)) :=
  TraceAnalyticStableMotiveQuasicategory.δ (3 : Fin 4) simplex

/-- The zeroth face keeps the last two short edges. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceZero_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexFaceZero simplex =
      ComposableArrows.mk₂
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexSecondEdge simplex)
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexThirdEdge simplex) :=
  rfl

/-- The first face skips the first interior vertex. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceOne_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexFaceOne simplex =
      ComposableArrows.mk₂
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexLeftPairEdge simplex)
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexThirdEdge simplex) :=
  rfl

/-- The second face skips the second interior vertex. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceTwo_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexFaceTwo simplex =
      ComposableArrows.mk₂
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFirstEdge simplex)
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexRightPairEdge simplex) :=
  rfl

/-- The third face keeps the first two short edges. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceThree_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexFaceThree simplex =
      ComposableArrows.mk₂
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFirstEdge simplex)
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexSecondEdge simplex) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
