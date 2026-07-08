import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Owner

/-!
# Faces of analytic stable motive two-simplices

This owner file exposes the three face maps of a two-simplex in the analytic
stable motive nerve.  The faces are concrete one-simplices: the second edge,
the composite edge, and the first edge.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The zeroth face of an analytic stable motive two-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceZero
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  TraceAnalyticStableMotiveQuasicategory.δ (0 : Fin 3) simplex

/-- The first face of an analytic stable motive two-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceOne
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  TraceAnalyticStableMotiveQuasicategory.δ (1 : Fin 3) simplex

/-- The second face of an analytic stable motive two-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceTwo
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  TraceAnalyticStableMotiveQuasicategory.δ (2 : Fin 3) simplex

/-- The zeroth face is the second edge of the two-simplex. -/
theorem TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceZero_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory
        .twoSimplexFaceZero simplex =
      ComposableArrows.mk₁
        (TraceAnalyticStableMotiveQuasicategory
          .twoSimplexSecondEdge simplex) :=
  rfl

/-- The first face is the composite edge of the two-simplex. -/
theorem TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceOne_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory
        .twoSimplexFaceOne simplex =
      ComposableArrows.mk₁
        (TraceAnalyticStableMotiveQuasicategory
          .twoSimplexCompositeEdge simplex) :=
  rfl

/-- The second face is the first edge of the two-simplex. -/
theorem TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceTwo_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory
        .twoSimplexFaceTwo simplex =
      ComposableArrows.mk₁
        (TraceAnalyticStableMotiveQuasicategory
          .twoSimplexFirstEdge simplex) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
