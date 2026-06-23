import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseCellBoundary

/-!
# Tail telescoping algebra for semicircle staircase horizontal sides

This file owns the interval-additivity algebra that turns a finite chain of
right-tail differences into endpoint tails and connector corrections.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- A finite chain of right-tail differences telescopes to the endpoint tails,
subtracting the intermediate connectors and the final reverse connector.

This is the interval-additivity owner lemma behind the horizontal part of the
staircase collar assembly.  The hypotheses are intentionally explicit:
splitting interval integrals in mathlib requires `IntervalIntegrable`, so the
geometry layer must supply continuity/integrability before using this lemma. -/
theorem Complex.sum_rightTail_integral_sub_successor_eq_endpoint_sub_connectors
    (F : ℕ → ℝ → ℂ)
    (x : ℕ → ℝ)
    (B : ℝ)
    (m : ℕ)
    (hconn :
      ∀ k ∈ Finset.range (m + 1),
        IntervalIntegrable (F k) volume (x k) (x (k + 1)))
    (htail :
      ∀ k ∈ Finset.range (m + 1),
        IntervalIntegrable (F k) volume (x (k + 1)) B)
    (hend_seg :
      IntervalIntegrable (F (m + 1)) volume (x 0) (x (m + 1)))
    (hend_tail :
      IntervalIntegrable (F (m + 1)) volume (x (m + 1)) B) :
    (∑ k in Finset.range (m + 1),
        ((∫ t : ℝ in (x (k + 1))..B, F k t) -
          (∫ t : ℝ in (x (k + 1))..B, F (k + 1) t))) =
      (∫ t : ℝ in (x 0)..B, F 0 t) -
        (∫ t : ℝ in (x 0)..B, F (m + 1) t) -
          (∑ k in Finset.range (m + 1),
            ∫ t : ℝ in (x k)..(x (k + 1)), F k t) -
          (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t) := by
  let T : ℕ → ℂ := fun k => ∫ t : ℝ in (x k)..B, F k t
  let C : ℕ → ℂ := fun k => ∫ t : ℝ in (x k)..(x (k + 1)), F k t
  have hsplit :
      ∀ k ∈ Finset.range (m + 1),
        (∫ t : ℝ in (x (k + 1))..B, F k t) = T k - C k := by
    intro k hk
    have hadd :
        (∫ t : ℝ in (x k)..(x (k + 1)), F k t) +
            (∫ t : ℝ in (x (k + 1))..B, F k t) =
          ∫ t : ℝ in (x k)..B, F k t :=
      intervalIntegral.integral_add_adjacent_intervals
        (hconn k hk) (htail k hk)
    show
      (∫ t : ℝ in (x (k + 1))..B, F k t) =
        (∫ t : ℝ in (x k)..B, F k t) -
          (∫ t : ℝ in (x k)..(x (k + 1)), F k t)
    exact eq_sub_of_add_eq' hadd
  have hend :
      T (m + 1) =
        (∫ t : ℝ in (x 0)..B, F (m + 1) t) +
          (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t) := by
    have hadd :
        (∫ t : ℝ in (x 0)..(x (m + 1)), F (m + 1) t) +
            (∫ t : ℝ in (x (m + 1))..B, F (m + 1) t) =
          ∫ t : ℝ in (x 0)..B, F (m + 1) t :=
      intervalIntegral.integral_add_adjacent_intervals hend_seg hend_tail
    show
      (∫ t : ℝ in (x (m + 1))..B, F (m + 1) t) =
        (∫ t : ℝ in (x 0)..B, F (m + 1) t) +
          (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t)
    have htail :
        (∫ t : ℝ in (x (m + 1))..B, F (m + 1) t) =
          (∫ t : ℝ in (x 0)..B, F (m + 1) t) -
            (∫ t : ℝ in (x 0)..(x (m + 1)), F (m + 1) t) :=
      eq_sub_of_add_eq' hadd
    calc
      (∫ t : ℝ in (x (m + 1))..B, F (m + 1) t) =
          (∫ t : ℝ in (x 0)..B, F (m + 1) t) -
            (∫ t : ℝ in (x 0)..(x (m + 1)), F (m + 1) t) := htail
      _ = (∫ t : ℝ in (x 0)..B, F (m + 1) t) +
            (-(∫ t : ℝ in (x 0)..(x (m + 1)), F (m + 1) t)) := by
        exact sub_eq_add_neg
          (∫ t : ℝ in (x 0)..B, F (m + 1) t)
          (∫ t : ℝ in (x 0)..(x (m + 1)), F (m + 1) t)
      _ = (∫ t : ℝ in (x 0)..B, F (m + 1) t) +
            (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t) := by
        exact congrArg
          (fun u : ℂ => (∫ t : ℝ in (x 0)..B, F (m + 1) t) + u)
          (Eq.symm
            (intervalIntegral.integral_symm
              (a := x 0)
              (b := x (m + 1))
              (f := fun t : ℝ => F (m + 1) t)))
  have htel :
      (∑ k in Finset.range (m + 1), ((T k - C k) - T (k + 1))) =
        T 0 - T (m + 1) - ∑ k in Finset.range (m + 1), C k := by
    exact Complex.sum_shift_sub_segment_telescope T C m
  calc
    (∑ k in Finset.range (m + 1),
        ((∫ t : ℝ in (x (k + 1))..B, F k t) -
          (∫ t : ℝ in (x (k + 1))..B, F (k + 1) t))) =
        ∑ k in Finset.range (m + 1), ((T k - C k) - T (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact
        congrArg
          (fun z : ℂ => z - T (k + 1))
          (hsplit k hk)
    _ = T 0 - T (m + 1) - ∑ k in Finset.range (m + 1), C k := htel
    _ =
      (∫ t : ℝ in (x 0)..B, F 0 t) -
        (∫ t : ℝ in (x 0)..B, F (m + 1) t) -
          (∑ k in Finset.range (m + 1),
            ∫ t : ℝ in (x k)..(x (k + 1)), F k t) -
          (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t) := by
      show
        (∫ t : ℝ in (x 0)..B, F 0 t) -
          (∫ t : ℝ in (x (m + 1))..B, F (m + 1) t) -
          (∑ k in Finset.range (m + 1),
            ∫ t : ℝ in (x k)..(x (k + 1)), F k t) =
        (∫ t : ℝ in (x 0)..B, F 0 t) -
          (∫ t : ℝ in (x 0)..B, F (m + 1) t) -
          (∑ k in Finset.range (m + 1),
            ∫ t : ℝ in (x k)..(x (k + 1)), F k t) -
          (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t)
      exact
        Eq.trans
          (congrArg
            (fun z : ℂ =>
              (∫ t : ℝ in (x 0)..B, F 0 t) - z -
                (∑ k in Finset.range (m + 1),
                  ∫ t : ℝ in (x k)..(x (k + 1)), F k t))
            hend)
          (Complex.sub_add_sub_reassociate_endpoint
            (∫ t : ℝ in (x 0)..B, F 0 t)
            (∫ t : ℝ in (x 0)..B, F (m + 1) t)
            (∑ k in Finset.range (m + 1),
              ∫ t : ℝ in (x k)..(x (k + 1)), F k t)
            (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t))

end

end LFunctions
end Boundary
