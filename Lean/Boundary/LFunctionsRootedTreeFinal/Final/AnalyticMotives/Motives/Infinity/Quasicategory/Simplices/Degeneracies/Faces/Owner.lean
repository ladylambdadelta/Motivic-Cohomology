import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Degeneracies.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Faces.Owner

/-!
# Faces of degenerate analytic stable motive two-simplices

This owner file records the concrete face calculations for the two
degeneracies of a one-simplex in the analytic stable motive nerve.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The zeroth face of the zeroth degeneracy is the original one-simplex
edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.degeneracyZero_faceZero
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceZero
        (TraceAnalyticStableMotiveQuasicategory
          .oneSimplexDegeneracyZero simplex) =
      ComposableArrows.mk₁ (simplex.map' 0 1) :=
  rfl

/-- The first face of the zeroth degeneracy is the original one-simplex
edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.degeneracyZero_faceOne
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceOne
        (TraceAnalyticStableMotiveQuasicategory
          .oneSimplexDegeneracyZero simplex) =
      ComposableArrows.mk₁ (simplex.map' 0 1) :=
  Eq.trans
    (TraceAnalyticStableMotiveQuasicategory
      .twoSimplexFaceOne_eq
      (TraceAnalyticStableMotiveQuasicategory
        .oneSimplexDegeneracyZero simplex))
    (congrArg
      ComposableArrows.mk₁
      (TraceAnalyticStableMotiveQuasicategory
        .oneSimplexDegeneracyZero_composite simplex))

/-- The second face of the zeroth degeneracy is the identity at the source. -/
theorem TraceAnalyticStableMotiveQuasicategory.degeneracyZero_faceTwo
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceTwo
        (TraceAnalyticStableMotiveQuasicategory
          .oneSimplexDegeneracyZero simplex) =
      TraceAnalyticStableMotiveQuasicategory.identityOneSimplex
        (simplex.obj' 0) :=
  rfl

/-- The zeroth face of the first degeneracy is the identity at the target. -/
theorem TraceAnalyticStableMotiveQuasicategory.degeneracyOne_faceZero
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceZero
        (TraceAnalyticStableMotiveQuasicategory
          .oneSimplexDegeneracyOne simplex) =
      TraceAnalyticStableMotiveQuasicategory.identityOneSimplex
        (simplex.obj' 1) :=
  rfl

/-- The first face of the first degeneracy is the original one-simplex edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.degeneracyOne_faceOne
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceOne
        (TraceAnalyticStableMotiveQuasicategory
          .oneSimplexDegeneracyOne simplex) =
      ComposableArrows.mk₁ (simplex.map' 0 1) :=
  Eq.trans
    (TraceAnalyticStableMotiveQuasicategory
      .twoSimplexFaceOne_eq
      (TraceAnalyticStableMotiveQuasicategory
        .oneSimplexDegeneracyOne simplex))
    (congrArg
      ComposableArrows.mk₁
      (TraceAnalyticStableMotiveQuasicategory
        .oneSimplexDegeneracyOne_composite simplex))

/-- The second face of the first degeneracy is the original one-simplex
edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.degeneracyOne_faceTwo
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 1))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexFaceTwo
        (TraceAnalyticStableMotiveQuasicategory
          .oneSimplexDegeneracyOne simplex) =
      ComposableArrows.mk₁ (simplex.map' 0 1) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
