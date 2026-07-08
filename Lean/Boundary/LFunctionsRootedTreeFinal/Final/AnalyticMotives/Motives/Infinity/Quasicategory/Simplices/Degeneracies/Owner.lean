import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Identity.Owner

/-!
# Degeneracies of analytic stable motive one-simplices

This owner file identifies the two degeneracies of a one-simplex in the
analytic stable motive nerve with the concrete left and right unit
two-simplices.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The zeroth degeneracy of an analytic stable motive one-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.oneSimplexDegeneracyZero
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 2)) :=
  TraceAnalyticStableMotiveQuasicategory.σ (0 : Fin 2) simplex

/-- The first degeneracy of an analytic stable motive one-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.oneSimplexDegeneracyOne
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory.obj
      (Opposite.op (SimplexCategory.mk 2)) :=
  TraceAnalyticStableMotiveQuasicategory.σ (1 : Fin 2) simplex

/-- The zeroth degeneracy duplicates the source object and gives the
left-unit two-simplex. -/
theorem TraceAnalyticStableMotiveQuasicategory.oneSimplexDegeneracyZero_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory
        .oneSimplexDegeneracyZero simplex =
      TraceAnalyticStableMotiveQuasicategory
        .leftUnitTwoSimplex (simplex.map' 0 1) :=
  rfl

/-- The first degeneracy duplicates the target object and gives the
right-unit two-simplex. -/
theorem TraceAnalyticStableMotiveQuasicategory.oneSimplexDegeneracyOne_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory
        .oneSimplexDegeneracyOne simplex =
      TraceAnalyticStableMotiveQuasicategory
        .rightUnitTwoSimplex (simplex.map' 0 1) :=
  rfl

/-- The composite edge of the zeroth degeneracy is the original one-simplex
edge. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.oneSimplexDegeneracyZero_composite
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    (TraceAnalyticStableMotiveQuasicategory
      .oneSimplexDegeneracyZero simplex).map' 0 2 =
      simplex.map' 0 1 :=
  Eq.trans
    (congrArg
      (fun degenerate =>
        degenerate.map' 0 2)
      (TraceAnalyticStableMotiveQuasicategory
        .oneSimplexDegeneracyZero_eq simplex))
    (TraceAnalyticStableMotiveQuasicategory
      .leftUnitTwoSimplex_composite (simplex.map' 0 1))

/-- The composite edge of the first degeneracy is the original one-simplex
edge. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.oneSimplexDegeneracyOne_composite
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    (TraceAnalyticStableMotiveQuasicategory
      .oneSimplexDegeneracyOne simplex).map' 0 2 =
      simplex.map' 0 1 :=
  Eq.trans
    (congrArg
      (fun degenerate =>
        degenerate.map' 0 2)
      (TraceAnalyticStableMotiveQuasicategory
        .oneSimplexDegeneracyOne_eq simplex))
    (TraceAnalyticStableMotiveQuasicategory
      .rightUnitTwoSimplex_composite (simplex.map' 0 1))

end AnalyticMotives
end LFunctions
end Boundary
