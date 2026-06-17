import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseVerticalAssembly

/-!
# Boundary algebra for semicircle staircase cells

This file owns the finite-sum algebra used to collect the already-identified
horizontal, outer-vertical, and inner-vertical staircase boundary pieces.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Abstract finite-sum collection for the staircase-cell boundary pieces. -/
theorem Complex.sum_staircaseCellBoundary_parts_collect
    {ι : Type*}
    (s : Finset ι)
    (H T O J : ι → ℂ)
    (bottom top horizontal topConnector outer inner tangent : ℂ)
    (hhorizontal : Finset.sum s (fun k => H k - T k) =
      bottom - top - horizontal - topConnector)
    (houter : Finset.sum s (fun k => O k) = outer)
    (hinner : Finset.sum s (fun k => tangent * J k) = inner) :
    Finset.sum s (fun k => (H k - T k) + tangent * O k - tangent * J k) =
      bottom - top + tangent * outer -
        ((horizontal + inner) + topConnector) := by
  have hsplit_sub :
      Finset.sum s (fun k => (H k - T k) + tangent * O k - tangent * J k) =
        Finset.sum s (fun k => (H k - T k) + tangent * O k) -
          Finset.sum s (fun k => tangent * J k) :=
    Finset.sum_sub_distrib
  have hsplit_add :
      Finset.sum s (fun k => (H k - T k) + tangent * O k) =
        Finset.sum s (fun k => H k - T k) +
          Finset.sum s (fun k => tangent * O k) :=
    Finset.sum_add_distrib
  have houter_mul :
      Finset.sum s (fun k => tangent * O k) = tangent * outer := by
    exact
      Eq.trans
        (Finset.mul_sum (s := s) (f := O) tangent).symm
        (congrArg (fun z : ℂ => tangent * z) houter)
  calc
    Finset.sum s (fun k => (H k - T k) + tangent * O k - tangent * J k) =
        Finset.sum s (fun k => (H k - T k) + tangent * O k) -
          Finset.sum s (fun k => tangent * J k) := hsplit_sub
    _ =
        (Finset.sum s (fun k => H k - T k) +
          Finset.sum s (fun k => tangent * O k)) -
          Finset.sum s (fun k => tangent * J k) :=
      congrArg
        (fun z : ℂ => z - Finset.sum s (fun k => tangent * J k))
        hsplit_add
    _ =
        ((bottom - top - horizontal - topConnector) +
          tangent * outer) - inner :=
      congrArg₂
        (fun A B : ℂ => A - B)
        (congrArg₂
          (fun A B : ℂ => A + B)
          hhorizontal
          houter_mul)
        hinner
    _ =
      bottom - top + tangent * outer -
        ((horizontal + inner) + topConnector) :=
      Complex.rightPolygonalHalfCollarBoundary_collect
        bottom top horizontal topConnector outer inner tangent

end

end LFunctions
end Boundary
