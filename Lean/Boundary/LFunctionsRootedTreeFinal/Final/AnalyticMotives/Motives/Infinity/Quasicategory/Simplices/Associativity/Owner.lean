import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Simplices.Owner

/-!
# Associativity in analytic stable motive three-simplices

This owner file records the concrete associativity encoded by a three-simplex
of the analytic stable motive nerve.  The total edge of a composable triple is
the threefold composite in either parenthesization.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first short edge of an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexFirstEdge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    simplex.obj' 0 ⟶ simplex.obj' 1 :=
  simplex.map' 0 1

/-- The second short edge of an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexSecondEdge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    simplex.obj' 1 ⟶ simplex.obj' 2 :=
  simplex.map' 1 2

/-- The third short edge of an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexThirdEdge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    simplex.obj' 2 ⟶ simplex.obj' 3 :=
  simplex.map' 2 3

/-- The total edge of an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexTotalEdge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    simplex.obj' 0 ⟶ simplex.obj' 3 :=
  simplex.map' 0 3

/-- The left two-edge composite in an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexLeftPairEdge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    simplex.obj' 0 ⟶ simplex.obj' 2 :=
  simplex.map' 0 2

/-- The right two-edge composite in an analytic stable motive three-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.threeSimplexRightPairEdge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    simplex.obj' 1 ⟶ simplex.obj' 3 :=
  simplex.map' 1 3

/-- The left two-edge composite is the composite of the first two short
edges. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexLeftPairEdge_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexLeftPairEdge simplex =
      TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFirstEdge simplex ≫
        TraceAnalyticStableMotiveQuasicategory
          .threeSimplexSecondEdge simplex :=
  ComposableArrows.map'_comp simplex 0 1 2

/-- The right two-edge composite is the composite of the last two short
edges. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexRightPairEdge_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexRightPairEdge simplex =
      TraceAnalyticStableMotiveQuasicategory
          .threeSimplexSecondEdge simplex ≫
        TraceAnalyticStableMotiveQuasicategory
          .threeSimplexThirdEdge simplex :=
  ComposableArrows.map'_comp simplex 1 2 3

/-- The total edge is the left-paired composite followed by the third short
edge. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexTotalEdge_left
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexTotalEdge simplex =
      (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFirstEdge simplex ≫
        TraceAnalyticStableMotiveQuasicategory
          .threeSimplexSecondEdge simplex) ≫
        TraceAnalyticStableMotiveQuasicategory
          .threeSimplexThirdEdge simplex :=
  Eq.trans
    (ComposableArrows.map'_comp simplex 0 2 3)
    (congrArg
      (fun edge =>
        edge ≫
          TraceAnalyticStableMotiveQuasicategory
            .threeSimplexThirdEdge simplex)
      (TraceAnalyticStableMotiveQuasicategory
        .threeSimplexLeftPairEdge_eq simplex))

/-- The total edge is the first short edge followed by the right-paired
composite. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplexTotalEdge_right
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexTotalEdge simplex =
      TraceAnalyticStableMotiveQuasicategory
          .threeSimplexFirstEdge simplex ≫
        (TraceAnalyticStableMotiveQuasicategory
            .threeSimplexSecondEdge simplex ≫
          TraceAnalyticStableMotiveQuasicategory
            .threeSimplexThirdEdge simplex) :=
  Eq.trans
    (ComposableArrows.map'_comp simplex 0 1 3)
    (congrArg
      (fun edge =>
        TraceAnalyticStableMotiveQuasicategory
            .threeSimplexFirstEdge simplex ≫
          edge)
      (TraceAnalyticStableMotiveQuasicategory
        .threeSimplexRightPairEdge_eq simplex))

/-- The two parenthesizations of a composable triple in an analytic stable
motive three-simplex agree because both are the total edge of the
three-simplex. -/
theorem TraceAnalyticStableMotiveQuasicategory.threeSimplex_associativity
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3))) :
    (TraceAnalyticStableMotiveQuasicategory
        .threeSimplexFirstEdge simplex ≫
      TraceAnalyticStableMotiveQuasicategory
        .threeSimplexSecondEdge simplex) ≫
      TraceAnalyticStableMotiveQuasicategory
        .threeSimplexThirdEdge simplex =
    TraceAnalyticStableMotiveQuasicategory
        .threeSimplexFirstEdge simplex ≫
      (TraceAnalyticStableMotiveQuasicategory
          .threeSimplexSecondEdge simplex ≫
        TraceAnalyticStableMotiveQuasicategory
          .threeSimplexThirdEdge simplex) :=
  Eq.trans
    (Eq.symm
      (TraceAnalyticStableMotiveQuasicategory
        .threeSimplexTotalEdge_left simplex))
    (TraceAnalyticStableMotiveQuasicategory
      .threeSimplexTotalEdge_right simplex)

end AnalyticMotives
end LFunctions
end Boundary
