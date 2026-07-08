import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Owner

/-!
# Simplices of the analytic stable motive quasicategory

This owner file exposes the concrete simplices of the nerve presentation of
analytic stable motives.  An `n`-simplex is not extra synthetic structure: it
is a composable chain of `n` morphisms in the Verdier-localized analytic stable
motive category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The `n`-simplices of the analytic stable motive nerve are composable
chains of `n` morphisms in the analytic stable motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory_obj_eq_composableArrows
    (dimension : ℕ) :
    TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk dimension)) =
      ComposableArrows TraceAnalyticStableMotiveCategory dimension :=
  rfl

/-- The two-simplices of the analytic stable motive nerve are composable
pairs of morphisms in the analytic stable motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory_obj_two :
    TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2)) =
      ComposableArrows TraceAnalyticStableMotiveCategory 2 :=
  rfl

/-- The three-simplices of the analytic stable motive nerve are composable
triples of morphisms in the analytic stable motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory_obj_three :
    TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 3)) =
      ComposableArrows TraceAnalyticStableMotiveCategory 3 :=
  rfl

/-- The first short edge of an analytic stable motive two-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.twoSimplexFirstEdge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    simplex.obj' 0 ⟶ simplex.obj' 1 :=
  simplex.map' 0 1

/-- The second short edge of an analytic stable motive two-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.twoSimplexSecondEdge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    simplex.obj' 1 ⟶ simplex.obj' 2 :=
  simplex.map' 1 2

/-- The long edge of an analytic stable motive two-simplex. -/
def TraceAnalyticStableMotiveQuasicategory.twoSimplexCompositeEdge
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    simplex.obj' 0 ⟶ simplex.obj' 2 :=
  simplex.map' 0 2

/-- In a two-simplex of the analytic stable motive nerve, the long edge is
the composite of the two short edges. -/
theorem TraceAnalyticStableMotiveQuasicategory.twoSimplexCompositeEdge_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory
        .twoSimplexCompositeEdge simplex =
      TraceAnalyticStableMotiveQuasicategory
          .twoSimplexFirstEdge simplex ≫
        TraceAnalyticStableMotiveQuasicategory
          .twoSimplexSecondEdge simplex :=
  ComposableArrows.map'_comp simplex 0 1 2

/-- The first short edge projection is the `0 → 1` map of the underlying
composable pair. -/
theorem TraceAnalyticStableMotiveQuasicategory.twoSimplexFirstEdge_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory
        .twoSimplexFirstEdge simplex =
      simplex.map' 0 1 :=
  rfl

/-- The second short edge projection is the `1 → 2` map of the underlying
composable pair. -/
theorem TraceAnalyticStableMotiveQuasicategory.twoSimplexSecondEdge_eq
    (simplex :
      TraceAnalyticStableMotiveQuasicategory.obj
        (Opposite.op (SimplexCategory.mk 2))) :
    TraceAnalyticStableMotiveQuasicategory
        .twoSimplexSecondEdge simplex =
      simplex.map' 1 2 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
