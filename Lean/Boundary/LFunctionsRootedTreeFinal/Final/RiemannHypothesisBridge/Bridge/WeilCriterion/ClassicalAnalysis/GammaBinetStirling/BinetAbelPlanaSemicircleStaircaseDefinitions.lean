import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseArithmetic

/-!
# Basic right semicircle staircase definitions

This file owns the graph coordinate, safe staircase real coordinates, and the
elementary line-integral pieces used by the right semicircle staircase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter MeasureTheory

/-- Right circular graph coordinate at vertical coordinate `y`. -/
noncomputable def Complex.rightSemicircleGraphRe
    (ρ y : ℝ) : ℝ :=
  Real.sqrt (ρ ^ 2 - y ^ 2)

/-- Definitional expansion of the right semicircle graph coordinate. -/
theorem Complex.rightSemicircleGraphRe_eq_sqrt
    (ρ y : ℝ) :
    Complex.rightSemicircleGraphRe ρ y =
      Real.sqrt (ρ ^ 2 - y ^ 2) :=
  rfl

/-- Safe vertical coordinate for one staircase cell: the larger of the two
endpoint graph values, hence at least the graph on monotone half-intervals. -/
noncomputable def Complex.rightSemicircleStaircaseSafeRe
    (ρ : ℝ)
    (m k : ℕ) : ℝ :=
  if Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
      0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1) then
    ρ
  else
    max
      (Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k))
      (Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)))

/-- On a staircase cell crossing height zero, the safe real coordinate is the
circle radius. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_radius_of_crossing
    (ρ : ℝ)
    (m k : ℕ)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ := by
  show
    (if Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1) then
      ρ
    else
      max
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k))
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)))) = ρ
  exact if_pos hcross

/-- On a staircase cell not crossing height zero, the safe real coordinate is
the maximum of the two endpoint graph values. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_endpointMax_of_not_crossing
    (ρ : ℝ)
    (m k : ℕ)
    (hcross :
      ¬ (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
      max
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k))
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1))) := by
  show
    (if Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1) then
      ρ
    else
      max
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k))
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)))) =
      max
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k))
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)))
  exact if_neg hcross

/-- Previous safe real coordinate used by the horizontal connector at the
bottom of the `k`th staircase cell. -/
noncomputable def Complex.rightSemicircleStaircasePrevSafeRe
    (ρ : ℝ)
    (m k : ℕ) : ℝ :=
  if k = 0 then
    0
  else
    Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1)

/-- The previous safe real coordinate at the first cell is zero. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_zero_owner
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = 0 := by
  show (if 0 = 0 then 0 else
    Complex.rightSemicircleStaircaseSafeRe ρ m (0 - 1)) = 0
  exact if_pos rfl

/-- At a successor cell, the previous safe coordinate is the preceding safe
coordinate. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_succ_owner
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m (k + 1) =
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  show (if k + 1 = 0 then 0 else
    Complex.rightSemicircleStaircaseSafeRe ρ m ((k + 1) - 1)) =
      Complex.rightSemicircleStaircaseSafeRe ρ m k
  calc
    (if k + 1 = 0 then 0 else
      Complex.rightSemicircleStaircaseSafeRe ρ m ((k + 1) - 1)) =
        Complex.rightSemicircleStaircaseSafeRe ρ m ((k + 1) - 1) :=
      if_neg (Nat.succ_ne_zero k)
    _ = Complex.rightSemicircleStaircaseSafeRe ρ m k :=
      congrArg
        (fun j : ℕ => Complex.rightSemicircleStaircaseSafeRe ρ m j)
        (Nat.succ_sub_one k)

/-- At a nonzero cell, the previous safe coordinate is the safe coordinate of
the predecessor cell. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_eq_safeRe_pred_of_ne_zero
    (ρ : ℝ)
    (m k : ℕ)
    (hk0 : k ≠ 0) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m k =
      Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) := by
  show (if k = 0 then 0 else
    Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1)) =
      Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1)
  exact if_neg hk0

/-- Horizontal connector at the bottom of a staircase cell. -/
noncomputable def Complex.rightSemicircleStaircaseHorizontalIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  ∫ x : ℝ in
    Complex.rightSemicircleStaircasePrevSafeRe ρ m k..
      Complex.rightSemicircleStaircaseSafeRe ρ m k,
    f (((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))

/-- Vertical side of a staircase cell. -/
noncomputable def Complex.rightSemicircleStaircaseVerticalIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  Complex.I *
    ∫ y : ℝ in
      Complex.rightSemicircleStaircaseY ρ m k..
        Complex.rightSemicircleStaircaseY ρ m (k + 1),
      f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
        Complex.I * (((c.im + y : ℝ) : ℂ)))

/-- Final horizontal connector from the last safe staircase coordinate to the
top tangent point. -/
noncomputable def Complex.rightSemicircleStaircaseTopConnectorIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  ∫ x : ℝ in
    Complex.rightSemicircleStaircaseSafeRe ρ m m..0,
    f (((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + ρ : ℝ) : ℂ)))

/-- A nonnegative radius has its negative endpoint below its positive endpoint. -/
theorem Complex.neg_radius_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    -ρ ≤ ρ := by
  have hneg_nonpos : -ρ ≤ 0 := neg_nonpos.mpr hρ
  exact le_trans hneg_nonpos hρ

end

end LFunctions
end Boundary
