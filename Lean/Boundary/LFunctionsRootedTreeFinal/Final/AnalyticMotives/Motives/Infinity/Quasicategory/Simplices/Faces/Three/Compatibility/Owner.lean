import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Faces.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Faces.Three.Owner

/-!
# Boundary compatibility for analytic stable motive three-simplex faces

This owner file records how the composite edge of each two-dimensional face
of an analytic stable motive three-simplex recovers the corresponding paired
or total edge of the original composable triple.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The composite edge of the zeroth face is the right paired edge. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceZero_composite
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexCompositeEdge
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFaceZero simplex) =
      TraceAnalyticStableMotiveQuasicategory
        .threeSimplexRightPairEdge simplex :=
  rfl

/-- The composite edge of the first face is the total edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceOne_composite
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexCompositeEdge
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFaceOne simplex) =
      TraceAnalyticStableMotiveQuasicategory
        .threeSimplexTotalEdge simplex :=
  rfl

/-- The composite edge of the second face is the total edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceTwo_composite
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexCompositeEdge
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFaceTwo simplex) =
      TraceAnalyticStableMotiveQuasicategory
        .threeSimplexTotalEdge simplex :=
  rfl

/-- The composite edge of the third face is the left paired edge. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.threeSimplexFaceThree_composite
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexCompositeEdge
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFaceThree simplex) =
      TraceAnalyticStableMotiveQuasicategory
        .threeSimplexLeftPairEdge simplex :=
  rfl

/-- The two middle faces have the same composite edge, namely the total edge
of the original three-simplex. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.threeSimplex_middleFaces_composite
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory.twoSimplexCompositeEdge
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFaceOne simplex) =
      TraceAnalyticStableMotiveQuasicategory.twoSimplexCompositeEdge
        (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFaceTwo simplex) :=
  Eq.trans
    (TraceAnalyticStableMotiveQuasicategory
      .threeSimplexFaceOne_composite simplex)
    (Eq.symm
      (TraceAnalyticStableMotiveQuasicategory
        .threeSimplexFaceTwo_composite simplex))

end AnalyticMotives
end LFunctions
end Boundary
