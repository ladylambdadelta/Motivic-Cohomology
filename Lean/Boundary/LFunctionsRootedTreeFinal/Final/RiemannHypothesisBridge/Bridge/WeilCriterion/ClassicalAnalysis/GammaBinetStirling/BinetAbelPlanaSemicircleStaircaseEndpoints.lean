import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseCellDomain

/-!
# Endpoint bookkeeping for right semicircle staircase geometry

This file owns the endpoint identities used when the finite staircase is
assembled into the polygonal right-half-collar boundary.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Top endpoint of the staircase height partition. -/
theorem Complex.rightSemicircleStaircaseY_last
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m (m + 1) = ρ := by
  show
    -ρ + (((m + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ) = ρ
  have hcast : ((m + 1 : ℕ) : ℝ) = (m + 1 : ℝ) := by
    exact Real.natCast_add_one_eq_real_add_one m
  have hden : (m + 1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rightSemicircleStaircase_denominator_pos m)
  have hratio : ((m + 1 : ℕ) : ℝ) / (m + 1 : ℝ) = 1 :=
    Eq.mp
      (congrArg (fun x : ℝ => x / (m + 1 : ℝ) = 1) (Eq.symm hcast))
      (div_self hden)
  calc
    -ρ + (((m + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ) =
        -ρ + 1 * (2 * ρ) :=
      congrArg (fun r : ℝ => -ρ + r * (2 * ρ)) hratio
    _ = ρ :=
      Real.rightSemicircleStaircase_top_translate ρ

/-- The first previous-safe coordinate is the bottom tangent point. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_zero
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = 0 := by
  exact Complex.rightSemicircleStaircasePrevSafeRe_zero_owner ρ m

/-- Successor previous-safe coordinate is the preceding safe coordinate. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_succ
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m (k + 1) =
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  exact Complex.rightSemicircleStaircasePrevSafeRe_succ_owner ρ m k

/-- Bottom endpoint of the translated staircase height partition. -/
theorem Complex.rightSemicircleStaircaseY_zero_add_im
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    c.im + Complex.rightSemicircleStaircaseY ρ m 0 = c.im - ρ := by
  calc
    c.im + Complex.rightSemicircleStaircaseY ρ m 0 = c.im + -ρ :=
      congrArg (fun y : ℝ => c.im + y)
        (Complex.rightSemicircleStaircaseY_zero ρ m)
    _ = c.im - ρ := rfl

/-- Top endpoint of the translated staircase height partition. -/
theorem Complex.rightSemicircleStaircaseY_last_add_im
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    c.im + Complex.rightSemicircleStaircaseY ρ m (m + 1) = c.im + ρ := by
  exact
    congrArg (fun y : ℝ => c.im + y)
      (Complex.rightSemicircleStaircaseY_last ρ m)

/-- The first cell bottom side begins at the tangent point `c.re`. -/
theorem Complex.rightSemicircleStaircase_firstBottomStart
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = c.re := by
  calc
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = c.re + 0 :=
      congrArg (fun x : ℝ => c.re + x)
        (Complex.rightSemicircleStaircasePrevSafeRe_zero ρ m)
    _ = c.re := add_zero c.re

/-- The `k+1`st bottom side starts where the `k`th vertical side sits. -/
theorem Complex.rightSemicircleStaircase_succBottomStart
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m (k + 1) =
      c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  exact
    congrArg (fun x : ℝ => c.re + x)
      (Complex.rightSemicircleStaircasePrevSafeRe_succ ρ m k)

/-- The final top connector ends at the tangent point `c.re`. -/
theorem Complex.rightSemicircleStaircase_topConnectorEnd
    (c : ℂ)
    (_ρ : ℝ)
    (_m : ℕ) :
    c.re + (0 : ℝ) = c.re := by
  exact add_zero c.re

end

end LFunctions
end Boundary
