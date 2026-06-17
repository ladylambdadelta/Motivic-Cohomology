import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseVariation

/-!
# Height-grid and graph monotonicity for right semicircle staircases

This file owns the uniform staircase height-grid estimates and the two
one-sided monotonicity lemmas for the right semicircle graph.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory


/-- One step of the uniform staircase height grid. -/
theorem Complex.rightSemicircleStaircaseY_succ_sub
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m (k + 1) -
      Complex.rightSemicircleStaircaseY ρ m k =
        (2 * ρ) / (m + 1 : ℝ) := by
  have hsucc_sub :
      (((k + 1 : ℕ) : ℝ) - (k : ℝ)) = 1 := by
    calc
      (((k + 1 : ℕ) : ℝ) - (k : ℝ)) =
          ((k : ℝ) + 1) - (k : ℝ) := by
        exact congrArg (fun x : ℝ => x - (k : ℝ)) (Nat.cast_succ k)
      _ = 1 := add_sub_cancel_left (k : ℝ) 1
  show
    (-ρ + (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ)) -
      (-ρ + ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ)) =
        (2 * ρ) / (m + 1 : ℝ)
  calc
    (-ρ + (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ)) -
        (-ρ + ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ)) =
          (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ) -
            ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) := by
      exact add_sub_add_left_eq_sub
        ((((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ))
        (((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ))
        (-ρ)
    _ = ((((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) -
          ((k : ℝ) / (m + 1 : ℝ))) * (2 * ρ) := by
      exact Eq.symm
        (sub_mul
          (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ))
          ((k : ℝ) / (m + 1 : ℝ))
          (2 * ρ))
    _ = (((((k + 1 : ℕ) : ℝ) - (k : ℝ)) / (m + 1 : ℝ)) *
          (2 * ρ)) := by
      exact congrArg (fun x : ℝ => x * (2 * ρ))
        (div_sub_div_same (((k + 1 : ℕ) : ℝ)) (k : ℝ) (m + 1 : ℝ))
    _ = (1 / (m + 1 : ℝ)) * (2 * ρ) := by
      exact congrArg (fun x : ℝ => (x / (m + 1 : ℝ)) * (2 * ρ)) hsucc_sub
    _ = (2 * ρ) / (m + 1 : ℝ) :=
      one_div_mul_eq_div (m + 1 : ℝ) (2 * ρ)

/-- The staircase height grid is increasing. -/
theorem Complex.rightSemicircleStaircaseY_le_succ
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m k ≤
      Complex.rightSemicircleStaircaseY ρ m (k + 1) := by
  have hstep :
      0 ≤
        Complex.rightSemicircleStaircaseY ρ m (k + 1) -
          Complex.rightSemicircleStaircaseY ρ m k := by
    have hquot :
        0 ≤ (2 * ρ) / (m + 1 : ℝ) :=
      div_nonneg
        (mul_nonneg Real.rightSemicircleStaircase_two_nonneg hρ)
        (le_of_lt (Real.rightSemicircleStaircase_denominator_pos m))
    calc
      0 ≤ (2 * ρ) / (m + 1 : ℝ) := hquot
      _ =
          Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k :=
        Eq.symm (Complex.rightSemicircleStaircaseY_succ_sub ρ m k)
  exact sub_nonneg.mp hstep

/-- Grid points up to the midpoint have nonpositive height. -/
theorem Complex.rightSemicircleStaircaseY_nonpos_of_le_midpoint
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k ≤ (m + 1) / 2) :
    Complex.rightSemicircleStaircaseY ρ m k ≤ 0 := by
  have hmul_nat : k * 2 ≤ m + 1 :=
    Nat.mul_le_of_le_div 2 k (m + 1) hk
  have hmul_real : 2 * (k : ℝ) ≤ (m + 1 : ℝ) := by
    exact Real.two_mul_natCast_le_succ_of_nat_mul_le hmul_nat
  have hden_pos : 0 < (m + 1 : ℝ) :=
    Real.rightSemicircleStaircase_denominator_pos m
  have hratio_div : (2 * (k : ℝ)) / (m + 1 : ℝ) ≤ 1 :=
    (div_le_one hden_pos).mpr hmul_real
  have hratio : ((k : ℝ) / (m + 1 : ℝ)) * 2 ≤ 1 := by
    calc
      ((k : ℝ) / (m + 1 : ℝ)) * 2 =
          (2 * (k : ℝ)) / (m + 1 : ℝ) :=
        Real.div_mul_two_eq_two_mul_div (k : ℝ) (m + 1 : ℝ)
      _ ≤ 1 := hratio_div
  have hmul :
      ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) ≤ ρ := by
    calc
      ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) =
          (((k : ℝ) / (m + 1 : ℝ)) * 2) * ρ :=
        Real.ratio_mul_two_mul_radius ((k : ℝ) / (m + 1 : ℝ)) ρ
      _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hratio hρ
      _ = ρ := one_mul ρ
  show -ρ + ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) ≤ 0
  exact Real.neg_radius_add_le_zero_of_le_radius hmul

/-- The upper endpoint of every cell at or after the midpoint has
nonnegative height. -/
theorem Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : (m + 1) / 2 ≤ k) :
    0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1) := by
  have hle_pred : m + 1 ≤ 2 * k + 1 := by
    exact (Nat.div_le_iff_le_mul_add_pred Nat.two_pos).mp hk
  have hle_nat : m + 1 ≤ 2 * (k + 1) := by
    exact Nat.succ_le_two_mul_succ_of_le_two_mul_add_one hle_pred
  have hle_real : (m + 1 : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
    exact Real.succ_le_two_mul_succ_natCast_of_nat_le hle_nat
  have hden_pos : 0 < (m + 1 : ℝ) :=
    Real.rightSemicircleStaircase_denominator_pos m
  have hratio_div : 1 ≤ (2 * ((k + 1 : ℕ) : ℝ)) / (m + 1 : ℝ) := by
    exact (one_le_div hden_pos).mpr hle_real
  have hratio :
      1 ≤ (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * 2 := by
    calc
      1 ≤ (2 * ((k + 1 : ℕ) : ℝ)) / (m + 1 : ℝ) := hratio_div
      _ = (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * 2 :=
        Eq.symm
          (Real.div_mul_two_eq_two_mul_div
            (((k + 1 : ℕ) : ℝ)) (m + 1 : ℝ))
  have hmul :
      ρ ≤ (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ) := by
    calc
      ρ = 1 * ρ := Eq.symm (one_mul ρ)
      _ ≤ ((((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * 2) * ρ :=
          mul_le_mul_of_nonneg_right hratio hρ
      _ = (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ) :=
        Eq.symm
          (Real.ratio_mul_two_mul_radius
            (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) ρ)
  show 0 ≤ -ρ + (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ)
  exact Real.nonneg_neg_radius_add_of_radius_le hmul

/-- On the nonpositive half of the vertical diameter, the right semicircle
graph real coordinate is monotone increasing. -/
theorem Complex.rightSemicircleGraphRe_mono_nonpos
    (ρ : ℝ)
    {a b : ℝ}
    (hab : a ≤ b)
    (hb : b ≤ 0) :
    Complex.rightSemicircleGraphRe ρ a ≤
      Complex.rightSemicircleGraphRe ρ b := by
  have ha : a ≤ 0 := le_trans hab hb
  have habs : |b| ≤ |a| := by
    exact Real.abs_le_abs_of_nonpos_interval hab hb
  have hsq : b ^ 2 ≤ a ^ 2 := by
    have hp : |b| ^ 2 ≤ |a| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg b) habs 2
    exact
      Eq.mp
        (congrArg₂ (fun x y : ℝ => x ≤ y) (sq_abs b) (sq_abs a))
        hp
  have hrad : ρ ^ 2 - a ^ 2 ≤ ρ ^ 2 - b ^ 2 := by
    exact Real.sub_sq_le_sub_sq_of_sq_le hsq
  show Real.sqrt (ρ ^ 2 - a ^ 2) ≤ Real.sqrt (ρ ^ 2 - b ^ 2)
  exact Real.sqrt_le_sqrt hrad

/-- On the nonnegative half of the vertical diameter, the right semicircle
graph real coordinate is monotone decreasing. -/
theorem Complex.rightSemicircleGraphRe_antitone_nonneg
    (ρ : ℝ)
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b) :
    Complex.rightSemicircleGraphRe ρ b ≤
      Complex.rightSemicircleGraphRe ρ a := by
  have hb : 0 ≤ b := le_trans ha hab
  have habs : |a| ≤ |b| := by
    calc
      |a| = a := abs_of_nonneg ha
      _ ≤ b := hab
      _ = |b| := Eq.symm (abs_of_nonneg hb)
  have hsq : a ^ 2 ≤ b ^ 2 := by
    have hp : |a| ^ 2 ≤ |b| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg a) habs 2
    exact
      Eq.mp
        (congrArg₂ (fun x y : ℝ => x ≤ y) (sq_abs a) (sq_abs b))
        hp
  have hrad : ρ ^ 2 - b ^ 2 ≤ ρ ^ 2 - a ^ 2 := by
    exact Real.sub_sq_le_sub_sq_of_sq_le hsq
  show Real.sqrt (ρ ^ 2 - b ^ 2) ≤ Real.sqrt (ρ ^ 2 - a ^ 2)
  exact Real.sqrt_le_sqrt hrad

end

end LFunctions
end Boundary
