import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetBranchWallMovingSpike
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighted moving logarithmic spike estimates

This file owns the real-variable estimates for the denominator-side moving
logarithmic spike that remains after the Binet branch-wall pointwise
majorization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- Real numeral product `4 * 4 = 16`, as an explicit cast computation. -/
theorem Real.four_mul_four_eq_sixteen :
    (4 : ℝ) * 4 = 16 := by
  have hnat : (4 : ℕ) * 4 = 16 := by
    rfl
  calc
    (4 : ℝ) * 4 = (((4 : ℕ) * 4 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 4 4).symm
    _ = 16 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- Real numeral product `3 * 3 = 9`, as an explicit cast computation. -/
theorem Real.three_mul_three_eq_nine :
    (3 : ℝ) * 3 = 9 := by
  have hnat : (3 : ℕ) * 3 = 9 := by
    rfl
  calc
    (3 : ℝ) * 3 = (((3 : ℕ) * 3 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 3 3).symm
    _ = 9 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- Real numeral product `2 * 2 = 4`, as an explicit cast computation. -/
theorem Real.two_mul_two_eq_four :
    (2 : ℝ) * 2 = 4 := by
  have hnat : (2 : ℕ) * 2 = 4 := by
    rfl
  calc
    (2 : ℝ) * 2 = (((2 : ℕ) * 2 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 2 2).symm
    _ = 4 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- Real numeral product `3 * 4 = 12`, as an explicit cast computation. -/
theorem Real.three_mul_four_eq_twelve :
    (3 : ℝ) * 4 = 12 := by
  have hnat : (3 : ℕ) * 4 = 12 := by
    rfl
  calc
    (3 : ℝ) * 4 = (((3 : ℕ) * 4 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 3 4).symm
    _ = 12 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- Real numeral product `3 * 2 = 6`, as an explicit cast computation. -/
theorem Real.three_mul_two_eq_six :
    (3 : ℝ) * 2 = 6 := by
  have hnat : (3 : ℕ) * 2 = 6 := by
    rfl
  calc
    (3 : ℝ) * 2 = (((3 : ℕ) * 2 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 3 2).symm
    _ = 6 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- Real numeral product `2 * 4 = 8`, as an explicit cast computation. -/
theorem Real.two_mul_four_eq_eight :
    (2 : ℝ) * 4 = 8 := by
  have hnat : (2 : ℕ) * 4 = 8 := by
    rfl
  calc
    (2 : ℝ) * 4 = (((2 : ℕ) * 4 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 2 4).symm
    _ = 8 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- Real numeral square `3 ^ 2 = 9`. -/
theorem Real.three_sq_eq_nine :
    (3 : ℝ) ^ 2 = 9 := by
  exact Eq.trans (pow_two (3 : ℝ)) Real.three_mul_three_eq_nine

/-- Real numeral sum `2 + 1 = 3`. -/
theorem Real.two_add_one_eq_three :
    (2 : ℝ) + (1 : ℝ) = 3 := by
  exact _root_.two_add_one_eq_three

/-- Real numeral sum `3 + 5 = 8`. -/
theorem Real.three_add_five_eq_eight :
    (3 : ℝ) + 5 = 8 := by
  have hnat : (3 : ℕ) + 5 = 8 := by
    rfl
  calc
    (3 : ℝ) + 5 = (((3 : ℕ) + 5 : ℕ) : ℝ) := by
      exact (Nat.cast_add 3 5).symm
    _ = 8 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- Real numeral sum `6 + 6 = 12`. -/
theorem Real.six_add_six_eq_twelve :
    (6 : ℝ) + 6 = 12 := by
  have hnat : (6 : ℕ) + 6 = 12 := by
    rfl
  calc
    (6 : ℝ) + 6 = (((6 : ℕ) + 6 : ℕ) : ℝ) := by
      exact (Nat.cast_add 6 6).symm
    _ = 12 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- Real numeral difference `16 - 9 = 7`. -/
theorem Real.sixteen_sub_nine_eq_seven :
    (16 : ℝ) - 9 = 7 := by
  have hsum : (16 : ℝ) = 7 + 9 := by
    have hnat : (7 : ℕ) + 9 = 16 := by
      rfl
    exact
      Eq.symm
        (Eq.trans
          (Nat.cast_add 7 9).symm
          (congrArg (fun n : ℕ => (n : ℝ)) hnat))
  exact sub_eq_iff_eq_add.mpr hsum

/-- The real numeral `6` is nonnegative. -/
theorem Real.zero_le_six' :
    (0 : ℝ) ≤ 6 :=
  Nat.cast_nonneg 6

/-- The real numeral `5` is nonnegative. -/
theorem Real.zero_le_five' :
    (0 : ℝ) ≤ 5 :=
  Nat.cast_nonneg 5

/-- The real numeral `16` is nonnegative. -/
theorem Real.zero_le_sixteen' :
    (0 : ℝ) ≤ 16 :=
  Nat.cast_nonneg 16

/-- The real numeral `16` is positive. -/
theorem Real.zero_lt_sixteen' :
    (0 : ℝ) < 16 :=
  show (0 : ℝ) < ((16 : ℕ) : ℝ) from
    Nat.cast_pos.mpr (Nat.succ_pos 15)

/-- Squaring the quarter of a real number gives the sixteenth of the square. -/
theorem Real.sq_div_four_eq_sq_div_sixteen
    (x : ℝ) :
    (x / 4) ^ 2 = x ^ 2 / 16 := by
  calc
    (x / 4) ^ 2 = (x / 4) * (x / 4) := by
      exact pow_two (x / 4)
    _ = (x * x) / (4 * 4) := by
      exact div_mul_div_comm x 4 x 4
    _ = x ^ 2 / (4 * 4) := by
      exact congrArg (fun y : ℝ => y / (4 * 4)) (Eq.symm (pow_two x))
    _ = x ^ 2 / 16 := by
      exact congrArg (fun y : ℝ => x ^ 2 / y) Real.four_mul_four_eq_sixteen

/-- Squaring three quarters of a real number gives nine sixteenths of the
square. -/
theorem Real.three_mul_div_four_sq_eq_nine_mul_sq_div_sixteen
    (x : ℝ) :
    ((3 * x) / 4) ^ 2 = (9 * x ^ 2) / 16 := by
  calc
    ((3 * x) / 4) ^ 2 = ((3 * x) ^ 2) / 16 := by
      exact Real.sq_div_four_eq_sq_div_sixteen (3 * x)
    _ = ((3 ^ 2) * x ^ 2) / 16 := by
      exact congrArg (fun y : ℝ => y / 16) (mul_pow 3 x 2)
    _ = (9 * x ^ 2) / 16 := by
      exact congrArg (fun y : ℝ => y * x ^ 2 / 16) Real.three_sq_eq_nine

/-- Square comparison implies the quarter-norm real-part comparison in the
right half-plane. -/
theorem Complex.binetSecondFormula_re_quarter_le_of_sq_quarter_le_re_sq
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hsq : (‖w‖ / 4) ^ 2 ≤ w.re ^ 2) :
    ‖w‖ / 4 ≤ w.re := by
  have hright_nonneg : 0 ≤ w.re :=
    le_of_lt hw_re_pos
  have hleft_sq :
      (‖w‖ / 4) ^ 2 =
        (‖w‖ / 4) * (‖w‖ / 4) :=
    pow_two (‖w‖ / 4)
  have hright_sq :
      w.re ^ 2 = w.re * w.re :=
    pow_two w.re
  have hsq_mul :
      (‖w‖ / 4) * (‖w‖ / 4) ≤ w.re * w.re := by
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ w.re * w.re)
        hleft_sq
        (Eq.subst
          (motive := fun x : ℝ => (‖w‖ / 4) ^ 2 ≤ x)
          hright_sq
          hsq)
  exact nonneg_le_nonneg_of_sq_le_sq hright_nonneg hsq_mul

/-- Real-coordinate square extraction for the moderate upper-center geometry:
if a nonnegative coordinate has square at least one sixteenth of the total
radius square, then it is at least one quarter of the radius. -/
theorem Real.quarter_le_of_sq_quarter_le_sq
    {N x : ℝ}
    (hN_nonneg : 0 ≤ N)
    (hx_nonneg : 0 ≤ x)
    (hsq : (N / 4) ^ 2 ≤ x ^ 2) :
    N / 4 ≤ x := by
  have hleft_nonneg : 0 ≤ N / 4 :=
    div_nonneg hN_nonneg zero_le_four
  have hleft_sq :
      (N / 4) ^ 2 = (N / 4) * (N / 4) :=
    pow_two (N / 4)
  have hright_sq :
      x ^ 2 = x * x :=
    pow_two x
  have hsq_mul :
      (N / 4) * (N / 4) ≤ x * x := by
    exact
      Eq.subst
        (motive := fun y : ℝ => y ≤ x * x)
        hleft_sq
        (Eq.subst
          (motive := fun y : ℝ => (N / 4) ^ 2 ≤ y)
          hright_sq
          hsq)
  exact nonneg_le_nonneg_of_sq_le_sq hx_nonneg hsq_mul

/-- Multiplying a nonnegative square by `1 / 16` is dominated by multiplying it
by `7 / 16`. -/
theorem Real.one_sixteenth_mul_sq_le_seven_sixteenths_mul_sq
    {N : ℝ}
    (hN_nonneg : 0 ≤ N) :
    ((1 : ℝ) / 16) * (N ^ 2) ≤ ((7 : ℝ) / 16) * (N ^ 2) := by
  have hcoeff_le : ((1 : ℝ) / 16) ≤ (7 : ℝ) / 16 := by
    have hone_le_seven : (1 : ℝ) ≤ 7 := by
      exact Nat.one_le_ofNat
    exact div_le_div_of_nonneg_right hone_le_seven Real.zero_le_sixteen'
  have hsq_nonneg : 0 ≤ N ^ 2 :=
    sq_nonneg N
  exact mul_le_mul_of_nonneg_right hcoeff_le hsq_nonneg

/-- Removing nine sixteenths of a square leaves seven sixteenths of that
square. -/
theorem Real.sub_nine_sixteenths_sq_eq_seven_sixteenths_sq
    (N : ℝ) :
    N ^ 2 - (9 * N ^ 2) / 16 = (7 * N ^ 2) / 16 := by
  have hsixteen_ne : (16 : ℝ) ≠ 0 :=
    ne_of_gt Real.zero_lt_sixteen'
  calc
    N ^ 2 - (9 * N ^ 2) / 16 =
        (16 * N ^ 2) / 16 - (9 * N ^ 2) / 16 := by
      exact congrArg
        (fun x : ℝ => x - (9 * N ^ 2) / 16)
        (Eq.symm (mul_div_cancel_left₀ (N ^ 2) hsixteen_ne))
    _ = ((16 * N ^ 2) - (9 * N ^ 2)) / 16 := by
      exact (sub_div (16 * N ^ 2) (9 * N ^ 2) 16).symm
    _ = ((16 - 9) * N ^ 2) / 16 := by
      exact congrArg (fun x : ℝ => x / 16)
        (Eq.symm (sub_mul (16 : ℝ) 9 (N ^ 2)))
    _ = (7 * N ^ 2) / 16 := by
      exact congrArg (fun x : ℝ => (x * N ^ 2) / 16)
        Real.sixteen_sub_nine_eq_seven

/-- The square of `N / 4` is one sixteenth of the square. -/
theorem Real.sq_div_four_eq_one_sixteenth_mul_sq
    (N : ℝ) :
    (N / 4) ^ 2 = ((1 : ℝ) / 16) * N ^ 2 := by
  calc
    (N / 4) ^ 2 = N ^ 2 / 16 := by
      exact Real.sq_div_four_eq_sq_div_sixteen N
    _ = ((1 : ℝ) * N ^ 2) / 16 := by
      exact congrArg (fun x : ℝ => x / 16) (Eq.symm (one_mul (N ^ 2)))
    _ = ((1 : ℝ) / 16) * N ^ 2 := by
      exact (div_mul_eq_mul_div (1 : ℝ) 16 (N ^ 2)).symm

/-- The square of `3N/4` is nine sixteenths of the square. -/
theorem Real.three_quarters_sq_eq_nine_sixteenths_mul_sq
    (N : ℝ) :
    ((3 * N) / 4) ^ 2 = ((9 : ℝ) / 16) * N ^ 2 := by
  calc
    ((3 * N) / 4) ^ 2 = (9 * N ^ 2) / 16 := by
      exact Real.three_mul_div_four_sq_eq_nine_mul_sq_div_sixteen N
    _ = ((9 : ℝ) / 16) * N ^ 2 := by
      exact (div_mul_eq_mul_div (9 : ℝ) 16 (N ^ 2)).symm

/-- A nonnegative coordinate bounded by `3N/4` leaves at least `(N/4)^2`
of square radius in the complementary coordinate. -/
theorem Real.sq_quarter_le_sq_sub_sq_of_nonneg_le_three_quarters
    {N y : ℝ}
    (hN_nonneg : 0 ≤ N)
    (hy_nonneg : 0 ≤ y)
    (hy_le : y ≤ (3 * N) / 4) :
    (N / 4) ^ 2 ≤ N ^ 2 - y ^ 2 := by
  have hthree_quarters_nonneg : 0 ≤ (3 * N) / 4 :=
    div_nonneg (mul_nonneg (le_of_lt Real.zero_lt_three) hN_nonneg) zero_le_four
  have hy_sq_le_three_quarters_sq :
      y ^ 2 ≤ ((3 * N) / 4) ^ 2 :=
    have hmul :
        y * y ≤ ((3 * N) / 4) * ((3 * N) / 4) :=
      mul_self_le_mul_self hy_nonneg hy_le
    have hy_sq : y ^ 2 = y * y :=
      pow_two y
    have htarget_sq :
        ((3 * N) / 4) ^ 2 =
          ((3 * N) / 4) * ((3 * N) / 4) :=
      pow_two ((3 * N) / 4)
    Eq.subst
      (motive := fun lhs : ℝ => lhs ≤ ((3 * N) / 4) ^ 2)
      hy_sq.symm
      (Eq.subst
        (motive := fun rhs : ℝ => y * y ≤ rhs)
        htarget_sq.symm
        hmul)
  have hthree_quarters_sq :
      ((3 * N) / 4) ^ 2 = ((9 : ℝ) / 16) * N ^ 2 :=
    Real.three_quarters_sq_eq_nine_sixteenths_mul_sq N
  have hy_sq_le_nine :
      y ^ 2 ≤ ((9 : ℝ) / 16) * N ^ 2 :=
    Eq.subst
      (motive := fun x : ℝ => y ^ 2 ≤ x)
      hthree_quarters_sq
      hy_sq_le_three_quarters_sq
  have hsub_le :
      N ^ 2 - ((9 : ℝ) / 16) * N ^ 2 ≤ N ^ 2 - y ^ 2 :=
    sub_le_sub_left hy_sq_le_nine (N ^ 2)
  have hsub_eq :
      N ^ 2 - ((9 : ℝ) / 16) * N ^ 2 = (7 * N ^ 2) / 16 := by
    have hnine :
        ((9 : ℝ) / 16) * N ^ 2 = (9 * N ^ 2) / 16 :=
      div_mul_eq_mul_div (9 : ℝ) 16 (N ^ 2)
    exact
      Eq.subst
        (motive := fun x : ℝ => N ^ 2 - x = (7 * N ^ 2) / 16)
        hnine.symm
        (Real.sub_nine_sixteenths_sq_eq_seven_sixteenths_sq N)
  have hquarter_eq :
      (N / 4) ^ 2 = ((1 : ℝ) / 16) * N ^ 2 :=
    Real.sq_div_four_eq_one_sixteenth_mul_sq N
  have hquarter_le_seven :
      (N / 4) ^ 2 ≤ (7 * N ^ 2) / 16 := by
    have hraw :
        ((1 : ℝ) / 16) * N ^ 2 ≤ ((7 : ℝ) / 16) * N ^ 2 :=
      Real.one_sixteenth_mul_sq_le_seven_sixteenths_mul_sq hN_nonneg
    have hseven :
        ((7 : ℝ) / 16) * N ^ 2 = (7 * N ^ 2) / 16 :=
      div_mul_eq_mul_div (7 : ℝ) 16 (N ^ 2)
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ (7 * N ^ 2) / 16)
        hquarter_eq.symm
        (Eq.subst
          (motive := fun x : ℝ => ((1 : ℝ) / 16) * N ^ 2 ≤ x)
          hseven
          hraw)
  exact
    le_trans
      hquarter_le_seven
      (Eq.subst
        (motive := fun x : ℝ => x ≤ N ^ 2 - y ^ 2)
        hsub_eq
        hsub_le)

/-- A nonnegative half is bounded by three quarters. -/
theorem Real.half_le_three_quarters_of_nonneg
    {N : ℝ}
    (hN_nonneg : 0 ≤ N) :
    N / 2 ≤ (3 * N) / 4 := by
  have htwo_le_three : (2 : ℝ) ≤ 3 := by
    have htwo_le_two_add_one : (2 : ℝ) ≤ 2 + 1 :=
      le_add_of_nonneg_right zero_le_one
    exact
      Eq.subst
        (motive := fun x : ℝ => (2 : ℝ) ≤ x)
        Real.two_add_one_eq_three
        htwo_le_two_add_one
  have htwoN_le_threeN : 2 * N ≤ 3 * N :=
    mul_le_mul_of_nonneg_right htwo_le_three hN_nonneg
  have hquarter_le :
      (2 * N) / 4 ≤ (3 * N) / 4 :=
    div_le_div_of_nonneg_right htwoN_le_threeN zero_le_four
  have hhalf_eq :
      N / 2 = (2 * N) / 4 := by
    have htwo_ne : (2 : ℝ) ≠ 0 :=
      ne_of_gt zero_lt_two
    calc
      N / 2 = (2 * N) / (2 * 2) := by
        exact (mul_div_mul_left N 2 htwo_ne).symm
      _ = (2 * N) / 4 := by
        exact congrArg (fun x : ℝ => (2 * N) / x)
          Real.two_mul_two_eq_four
  exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ (3 * N) / 4)
      hhalf_eq.symm
      hquarter_le

/-- In the right half-plane, a moderate upper-center branch-wall location
forces the real part to be at least one quarter of the norm. -/
theorem Complex.binetSecondFormula_re_quarter_le_of_moderateUpperCenter
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hleft : ‖w‖ / 2 ≤ w.im)
    (hright : w.im ≤ (3 * ‖w‖) / 4) :
    ‖w‖ / 4 ≤ w.re := by
  have hN_nonneg : 0 ≤ ‖w‖ :=
    norm_nonneg w
  have him_nonneg : 0 ≤ w.im :=
    le_trans
      (div_nonneg hN_nonneg zero_le_two)
      hleft
  have hresidual :
      (‖w‖ / 4) ^ 2 ≤ ‖w‖ ^ 2 - w.im ^ 2 :=
    Real.sq_quarter_le_sq_sub_sq_of_nonneg_le_three_quarters
      hN_nonneg him_nonneg hright
  have hre_sq_eq_residual :
      w.re ^ 2 = ‖w‖ ^ 2 - w.im ^ 2 := by
    calc
      w.re ^ 2 = w.re * w.re := by
        exact pow_two w.re
      _ = (w.re * w.re + w.im * w.im) - w.im * w.im := by
        exact (add_sub_cancel_right (w.re * w.re) (w.im * w.im)).symm
      _ = Complex.normSq w - w.im * w.im := by
        exact congrArg (fun x : ℝ => x - w.im * w.im)
          (Eq.symm (Complex.normSq_apply w))
      _ = ‖w‖ ^ 2 - w.im * w.im := by
        exact congrArg (fun x : ℝ => x - w.im * w.im)
          (Complex.normSq_eq_norm_sq w)
      _ = ‖w‖ ^ 2 - w.im ^ 2 := by
        exact congrArg (fun x : ℝ => ‖w‖ ^ 2 - x)
          (Eq.symm (pow_two w.im))
  have hsq :
      (‖w‖ / 4) ^ 2 ≤ w.re ^ 2 :=
    Eq.subst
      (motive := fun x : ℝ => (‖w‖ / 4) ^ 2 ≤ x)
      hre_sq_eq_residual.symm
      hresidual
  exact
    Complex.binetSecondFormula_re_quarter_le_of_sq_quarter_le_re_sq
      hw_re_pos hsq

/-- In the right half-plane, a nonnegative lower-center branch-wall location
forces the real part to be at least one quarter of the norm. -/
theorem Complex.binetSecondFormula_re_quarter_le_of_nonnegativeLowerCenter
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (him_nonneg : 0 ≤ w.im)
    (him_le_half : w.im ≤ ‖w‖ / 2) :
    ‖w‖ / 4 ≤ w.re := by
  have hN_nonneg : 0 ≤ ‖w‖ :=
    norm_nonneg w
  have hhalf_le_three_quarters :
      ‖w‖ / 2 ≤ (3 * ‖w‖) / 4 :=
    Real.half_le_three_quarters_of_nonneg hN_nonneg
  have him_le_three_quarters :
      w.im ≤ (3 * ‖w‖) / 4 :=
    le_trans him_le_half hhalf_le_three_quarters
  have hresidual :
      (‖w‖ / 4) ^ 2 ≤ ‖w‖ ^ 2 - w.im ^ 2 :=
    Real.sq_quarter_le_sq_sub_sq_of_nonneg_le_three_quarters
      hN_nonneg him_nonneg him_le_three_quarters
  have hre_sq_eq_residual :
      w.re ^ 2 = ‖w‖ ^ 2 - w.im ^ 2 := by
    calc
      w.re ^ 2 = w.re * w.re := by
        exact pow_two w.re
      _ = (w.re * w.re + w.im * w.im) - w.im * w.im := by
        exact (add_sub_cancel_right (w.re * w.re) (w.im * w.im)).symm
      _ = Complex.normSq w - w.im * w.im := by
        exact congrArg (fun x : ℝ => x - w.im * w.im)
          (Eq.symm (Complex.normSq_apply w))
      _ = ‖w‖ ^ 2 - w.im * w.im := by
        exact congrArg (fun x : ℝ => x - w.im * w.im)
          (Complex.normSq_eq_norm_sq w)
      _ = ‖w‖ ^ 2 - w.im ^ 2 := by
        exact congrArg (fun x : ℝ => ‖w‖ ^ 2 - x)
          (Eq.symm (pow_two w.im))
  have hsq :
      (‖w‖ / 4) ^ 2 ≤ w.re ^ 2 :=
    Eq.subst
      (motive := fun x : ℝ => (‖w‖ / 4) ^ 2 ≤ x)
      hre_sq_eq_residual.symm
      hresidual
  exact
    Complex.binetSecondFormula_re_quarter_le_of_sq_quarter_le_re_sq
      hw_re_pos hsq

/-- Endpoint-distance logarithm bounded by the standard half-power model. -/
theorem Real.binetSecondFormula_endpointDistanceLog_le_rpow_half
    {N u : ℝ}
    (hN_pos : 0 < N)
    (hu_pos : 0 < u) :
    Real.log ((3 * N) / u) ≤
      ((3 * N) / u) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) := by
  have harg_nonneg : 0 ≤ (3 * N) / u :=
    le_of_lt (div_pos (mul_pos Real.zero_lt_three hN_pos) hu_pos)
  exact
    Real.log_le_rpow_div harg_nonneg one_half_pos

/-- Weighted endpoint-distance logarithm bounded by the half-power endpoint
model. -/
theorem Complex.binetSecondFormula_endpointDistanceLog_weighted_le_rpow_half
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_left : ‖w‖ / 2 < t) :
    (2 * Real.log ((3 * ‖w‖) / (t - ‖w‖ / 2))) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 *
          (((3 * ‖w‖) / (t - ‖w‖ / 2)) ^ ((1 : ℝ) / 2) /
            ((1 : ℝ) / 2))) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  have hN_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hdist_pos : 0 < t - ‖w‖ / 2 :=
    sub_pos.mpr ht_left
  have hlog_le :
      Real.log ((3 * ‖w‖) / (t - ‖w‖ / 2)) ≤
        ((3 * ‖w‖) / (t - ‖w‖ / 2)) ^ ((1 : ℝ) / 2) /
          ((1 : ℝ) / 2) :=
    Real.binetSecondFormula_endpointDistanceLog_le_rpow_half
      hN_pos hdist_pos
  have hnum_le :
      2 * Real.log ((3 * ‖w‖) / (t - ‖w‖ / 2)) ≤
        2 *
          (((3 * ‖w‖) / (t - ‖w‖ / 2)) ^ ((1 : ℝ) / 2) /
            ((1 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hlog_le zero_le_two
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) :=
    le_of_lt (Real.exp_pos ((2 : ℝ) * Real.pi * t))
  exact div_le_div_of_nonneg_right hnum_le hden_nonneg

/-- On the lower-center side of the denominator branch wall, the weighted
moving logarithmic spike is bounded pointwise by the endpoint-distance model. -/
theorem Complex.binetSecondFormula_minusMovingLog_weighted_le_leftEndpointDistance
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_im_le_left : w.im ≤ ‖w‖ / 2)
    {t : ℝ}
    (ht_mem : t ∈ Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) :
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 * Real.log ((3 * ‖w‖) / (t - ‖w‖ / 2))) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  have hlog_le :
      Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
        Real.log ((3 * ‖w‖) / (t - ‖w‖ / 2)) :=
    Complex.binetSecondFormula_minusMovingLog_le_leftEndpointDistance_log
      hw_re_pos
      hw_im_le_left
      ht_mem.1
  have hnum_le :
      2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
        2 * Real.log ((3 * ‖w‖) / (t - ‖w‖ / 2)) :=
    mul_le_mul_of_nonneg_left hlog_le zero_le_two
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) :=
    le_of_lt (Real.exp_pos ((2 : ℝ) * Real.pi * t))
  exact div_le_div_of_nonneg_right hnum_le hden_nonneg

/-- On the lower-center side, the weighted moving logarithmic spike is bounded
by the endpoint half-power model. -/
theorem Complex.binetSecondFormula_minusMovingLog_weighted_le_endpointRpowHalf
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_im_le_left : w.im ≤ ‖w‖ / 2)
    {t : ℝ}
    (ht_mem : t ∈ Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) :
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 *
          (((3 * ‖w‖) / (t - ‖w‖ / 2)) ^ ((1 : ℝ) / 2) /
            ((1 : ℝ) / 2))) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  have hleft :
      (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
        (2 * Real.log ((3 * ‖w‖) / (t - ‖w‖ / 2))) /
          Real.exp ((2 : ℝ) * Real.pi * t) :=
    Complex.binetSecondFormula_minusMovingLog_weighted_le_leftEndpointDistance
      hw_re_pos hw_im_le_left ht_mem
  have hright :
      (2 * Real.log ((3 * ‖w‖) / (t - ‖w‖ / 2))) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
        (2 *
            (((3 * ‖w‖) / (t - ‖w‖ / 2)) ^ ((1 : ℝ) / 2) /
              ((1 : ℝ) / 2))) /
          Real.exp ((2 : ℝ) * Real.pi * t) :=
    Complex.binetSecondFormula_endpointDistanceLog_weighted_le_rpow_half
      hw_re_pos ht_mem.1
  exact le_trans hleft hright

/-- If the real part is a fixed positive fraction of the norm, then the
denominator-side moving logarithmic spike is bounded by a constant logarithm. -/
theorem Complex.binetSecondFormula_minusMovingLog_le_log_twelve_of_re_quarter
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_re_quarter : ‖w‖ / 4 ≤ w.re)
    (t : ℝ) :
    Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
      Real.log 12 := by
  have hN_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hmax_pos : 0 < max w.re |w.im - t| :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have hquarter_le_max : ‖w‖ / 4 ≤ max w.re |w.im - t| :=
    le_trans hw_re_quarter (le_max_left w.re |w.im - t|)
  have hN_le_four_max :
      ‖w‖ ≤ 4 * max w.re |w.im - t| := by
    have hfour_mul :
        4 * (‖w‖ / 4) ≤
          4 * max w.re |w.im - t| :=
      mul_le_mul_of_nonneg_left hquarter_le_max zero_le_four
    have hfour_cancel :
        4 * (‖w‖ / 4) = ‖w‖ := by
      have hfour_ne_zero : (4 : ℝ) ≠ 0 :=
        ne_of_gt zero_lt_four
      calc
        4 * (‖w‖ / 4) = (4 * ‖w‖) / 4 := by
          exact mul_div_assoc' 4 ‖w‖ 4
        _ = ‖w‖ := by
          exact mul_div_cancel_left₀ ‖w‖ hfour_ne_zero
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ 4 * max w.re |w.im - t|)
        hfour_cancel
        hfour_mul
  have hthreeN_le_twelve_max :
      3 * ‖w‖ ≤ 12 * max w.re |w.im - t| := by
    have hthree_mul :
        3 * ‖w‖ ≤ 3 * (4 * max w.re |w.im - t|) :=
      mul_le_mul_of_nonneg_left hN_le_four_max
        (le_of_lt Real.zero_lt_three)
    have hcoeff :
        3 * (4 * max w.re |w.im - t|) =
          12 * max w.re |w.im - t| := by
      calc
        3 * (4 * max w.re |w.im - t|) =
            (3 * 4) * max w.re |w.im - t| := by
          exact (mul_assoc (3 : ℝ) 4 (max w.re |w.im - t|)).symm
        _ = 12 * max w.re |w.im - t| := by
          exact congrArg (fun c : ℝ => c * max w.re |w.im - t|)
            Real.three_mul_four_eq_twelve
    exact le_trans hthree_mul (le_of_eq hcoeff)
  have harg_le :
      (3 * ‖w‖) / max w.re |w.im - t| ≤ 12 := by
    exact
      (div_le_iff₀ hmax_pos).mpr hthreeN_le_twelve_max
  have harg_pos :
      0 < (3 * ‖w‖) / max w.re |w.im - t| :=
    div_pos (mul_pos Real.zero_lt_three hN_pos) hmax_pos
  exact Real.log_le_log harg_pos harg_le

/-- Weighted constant-log comparison in the region where the real part is a
fixed positive fraction of the norm. -/
theorem Complex.binetSecondFormula_minusMovingLog_weighted_le_log_twelve_of_re_quarter
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_re_quarter : ‖w‖ / 4 ≤ w.re)
    (t : ℝ) :
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 * Real.log 12) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  have hlog_le :
      Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
        Real.log 12 :=
    Complex.binetSecondFormula_minusMovingLog_le_log_twelve_of_re_quarter
      hw_re_pos hw_re_quarter t
  have hnum_le :
      2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
        2 * Real.log 12 :=
    mul_le_mul_of_nonneg_left hlog_le zero_le_two
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) :=
    le_of_lt (Real.exp_pos ((2 : ℝ) * Real.pi * t))
  exact div_le_div_of_nonneg_right hnum_le hden_nonneg

/-- Integrated constant-log comparison in the region where the real part is a
fixed positive fraction of the norm. -/
theorem Complex.binetSecondFormula_minusMovingLog_integral_le_log_twelve_of_re_quarter
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_re_quarter : ‖w‖ / 4 ≤ w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log 12) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let F : ℝ → ℝ := fun t : ℝ =>
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 * Real.log 12) / Real.exp ((2 : ℝ) * Real.pi * t)
  have hF_integrable : IntegrableOn F S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let B : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / B t
    let Fcc : ℝ → ℝ := fun t : ℝ =>
      (2 * Real.log (A t)) / Real.exp ((2 : ℝ) * Real.pi * t)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hB_pos : ∀ t : ℝ, 0 < B t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hA_pos : ∀ t : ℝ, 0 < A t := by
      intro t
      exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hB_pos t)
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hB_cont : Continuous B :=
      continuous_const.sup hdist_cont
    have hA_cont : Continuous A :=
      continuous_const.div hB_cont (fun t => (hB_pos t).ne')
    have hlog_contOn :
        ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
      (hA_cont.continuousOn).log (fun t _ht => (hA_pos t).ne')
    have hnum_contOn :
        ContinuousOn (fun t : ℝ => 2 * Real.log (A t)) Scc :=
      continuousOn_const.mul hlog_contOn
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne :
        ∀ t : ℝ, t ∈ Scc →
          Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hFcc_contOn : ContinuousOn Fcc Scc :=
      hnum_contOn.div hden_cont.continuousOn hden_ne
    have hFcc_integrable : IntegrableOn Fcc Scc :=
      hFcc_contOn.integrableOn_Icc
    exact hFcc_integrable.mono_set Set.Ioc_subset_Icc_self
  have hG_integrable : IntegrableOn G S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let Gcc : ℝ → ℝ := fun t : ℝ =>
      (2 * Real.log 12) / Real.exp ((2 : ℝ) * Real.pi * t)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne :
        ∀ t : ℝ, t ∈ Scc →
          Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hGcc_contOn : ContinuousOn Gcc Scc :=
      continuousOn_const.div hden_cont.continuousOn hden_ne
    have hGcc_integrable : IntegrableOn Gcc Scc :=
      hGcc_contOn.integrableOn_Icc
    exact hGcc_integrable.mono_set Set.Ioc_subset_Icc_self
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, F t ≤ G t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t _ht =>
        Complex.binetSecondFormula_minusMovingLog_weighted_le_log_twelve_of_re_quarter
          hw_re_pos hw_re_quarter t)
  exact setIntegral_mono_ae_restrict hF_integrable hG_integrable hpoint

/-- Upper-center denominator branch-wall locations split into a moderate
center and a far-center region. -/
theorem Complex.binetSecondFormula_denominator_branchWall_upperCenter_split
    (w : ℂ) :
    w.im ≤ (3 * ‖w‖) / 4 ∨ (3 * ‖w‖) / 4 ≤ w.im := by
  exact le_total w.im ((3 * ‖w‖) / 4)

/-- A moderate upper-center location is still inside the bounded tail window. -/
theorem Complex.binetSecondFormula_denominator_branchWall_moderateUpperCenter_mem_boundedTailWindow
    {w : ℂ}
    (hleft : ‖w‖ / 2 ≤ w.im)
    (hright : w.im ≤ (3 * ‖w‖) / 4) :
    w.im ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖) := by
  have hnorm_nonneg : 0 ≤ ‖w‖ :=
    norm_nonneg w
  have hthree_quarter_le_two :
      (3 * ‖w‖) / 4 ≤ 2 * ‖w‖ := by
    have hthree_le_eight_const : (3 : ℝ) ≤ 8 := by
      have hthree_le_three_add_five : (3 : ℝ) ≤ 3 + 5 :=
        le_add_of_nonneg_right Real.zero_le_five'
      exact
        Eq.subst
          (motive := fun x : ℝ => (3 : ℝ) ≤ x)
          Real.three_add_five_eq_eight
          hthree_le_three_add_five
    have hthree_le_eight : (3 : ℝ) * ‖w‖ ≤ 8 * ‖w‖ :=
      mul_le_mul_of_nonneg_right
        hthree_le_eight_const
        hnorm_nonneg
    have hdiv_le :
        (3 * ‖w‖) / 4 ≤ (8 * ‖w‖) / 4 :=
      div_le_div_of_nonneg_right hthree_le_eight zero_le_four
    have height_div :
        (8 * ‖w‖) / 4 = 2 * ‖w‖ := by
      calc
        (8 * ‖w‖) / 4 = ((2 * 4) * ‖w‖) / 4 := by
          exact congrArg (fun c : ℝ => (c * ‖w‖) / 4)
            Real.two_mul_four_eq_eight.symm
        _ = (2 * (4 * ‖w‖)) / 4 := by
          exact congrArg (fun x : ℝ => x / 4)
            (mul_assoc (2 : ℝ) 4 ‖w‖)
        _ = 2 * ((4 * ‖w‖) / 4) := by
          exact mul_div_assoc (2 : ℝ) (4 * ‖w‖) 4
        _ = 2 * ‖w‖ := by
          have hfour_ne_zero : (4 : ℝ) ≠ 0 :=
            ne_of_gt zero_lt_four
          exact congrArg (fun x : ℝ => 2 * x)
            (mul_div_cancel_left₀ ‖w‖ hfour_ne_zero)
    exact le_trans hdiv_le (le_of_eq height_div)
  exact ⟨hleft, le_trans hright hthree_quarter_le_two⟩

/-- Integrated constant-log comparison on the moderate upper-center side of
the denominator branch wall. -/
theorem Complex.binetSecondFormula_minusMovingLog_integral_le_log_twelve_of_moderateUpperCenter
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hleft : ‖w‖ / 2 ≤ w.im)
    (hright : w.im ≤ (3 * ‖w‖) / 4) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log 12) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  have hquarter :
      ‖w‖ / 4 ≤ w.re :=
    Complex.binetSecondFormula_re_quarter_le_of_moderateUpperCenter
      hw_re_pos hleft hright
  exact
    Complex.binetSecondFormula_minusMovingLog_integral_le_log_twelve_of_re_quarter
      hw_re_pos hquarter

/-- Integrated constant-log comparison on the nonnegative lower-center side of
the denominator branch wall. -/
theorem Complex.binetSecondFormula_minusMovingLog_integral_le_log_twelve_of_nonnegativeLowerCenter
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (him_nonneg : 0 ≤ w.im)
    (him_le_half : w.im ≤ ‖w‖ / 2) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log 12) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  have hquarter :
      ‖w‖ / 4 ≤ w.re :=
    Complex.binetSecondFormula_re_quarter_le_of_nonnegativeLowerCenter
      hw_re_pos him_nonneg him_le_half
  exact
    Complex.binetSecondFormula_minusMovingLog_integral_le_log_twelve_of_re_quarter
      hw_re_pos hquarter

/-- If the branch-wall center is below the origin, then the denominator is at
least half the norm throughout the bounded tail window. -/
theorem Complex.binetSecondFormula_denominator_branchWall_distance_ge_halfNorm_of_im_nonpos
    {w : ℂ}
    (hw_im_nonpos : w.im ≤ 0)
    {t : ℝ}
    (ht_left : ‖w‖ / 2 ≤ t) :
    ‖w‖ / 2 ≤ max w.re |w.im - t| := by
  have ht_nonneg : 0 ≤ t :=
    le_trans (div_nonneg (norm_nonneg w) zero_le_two) ht_left
  have hdiff_nonpos : w.im - t ≤ 0 := by
    exact sub_nonpos.mpr (le_trans hw_im_nonpos ht_nonneg)
  have hdist_eq : |w.im - t| = t - w.im := by
    calc
      |w.im - t| = -(w.im - t) := by
        exact abs_of_nonpos hdiff_nonpos
      _ = t - w.im := by
        exact neg_sub w.im t
  have hhalf_le_dist : ‖w‖ / 2 ≤ |w.im - t| := by
    have hhalf_le_t_sub : ‖w‖ / 2 ≤ t - w.im := by
      have ht_le_t_sub : t ≤ t - w.im := by
        have hneg_nonneg : 0 ≤ -w.im :=
          neg_nonneg.mpr hw_im_nonpos
        have hadd : t + 0 ≤ t + -w.im :=
          add_le_add_left hneg_nonneg t
        have hleft : t + 0 = t :=
          add_zero t
        have hright : t + -w.im = t - w.im :=
          (sub_eq_add_neg t w.im).symm
        exact
          Eq.subst
            (motive := fun x : ℝ => t ≤ x)
            hright
            (Eq.subst
              (motive := fun x : ℝ => x ≤ t + -w.im)
              hleft
              hadd)
      exact le_trans ht_left ht_le_t_sub
    exact
      Eq.subst
        (motive := fun x : ℝ => ‖w‖ / 2 ≤ x)
        hdist_eq.symm
        hhalf_le_t_sub
  exact le_trans hhalf_le_dist (le_max_right w.re |w.im - t|)

/-- On the nonpositive-center lower side, the minus moving logarithmic spike is
bounded by the same harmless constant logarithm. -/
theorem Complex.binetSecondFormula_minusMovingLog_le_log_twelve_of_im_nonpos
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_im_nonpos : w.im ≤ 0)
    {t : ℝ}
    (ht_left : ‖w‖ / 2 ≤ t) :
    Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
      Real.log 12 := by
  have hN_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hmax_pos : 0 < max w.re |w.im - t| :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have hhalf_le_max :
      ‖w‖ / 2 ≤ max w.re |w.im - t| :=
    Complex.binetSecondFormula_denominator_branchWall_distance_ge_halfNorm_of_im_nonpos
      hw_im_nonpos ht_left
  have hN_le_two_max :
      ‖w‖ ≤ 2 * max w.re |w.im - t| := by
    have htwo_mul :
        2 * (‖w‖ / 2) ≤
          2 * max w.re |w.im - t| :=
      mul_le_mul_of_nonneg_left hhalf_le_max zero_le_two
    have htwo_cancel :
        2 * (‖w‖ / 2) = ‖w‖ := by
      exact Real.two_mul_div_two ‖w‖
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ 2 * max w.re |w.im - t|)
        htwo_cancel
        htwo_mul
  have hthreeN_le_twelve_max :
      3 * ‖w‖ ≤ 12 * max w.re |w.im - t| := by
    have hthree_mul :
        3 * ‖w‖ ≤ 3 * (2 * max w.re |w.im - t|) :=
      mul_le_mul_of_nonneg_left hN_le_two_max
        (le_of_lt Real.zero_lt_three)
    have htwo_to_twelve :
        3 * (2 * max w.re |w.im - t|) ≤
          12 * max w.re |w.im - t| := by
      have hmax_nonneg : 0 ≤ max w.re |w.im - t| :=
        le_of_lt hmax_pos
      have hsix_le_twelve : (6 : ℝ) ≤ 12 := by
        have hsix_le_six_add_six : (6 : ℝ) ≤ 6 + 6 :=
          le_add_of_nonneg_right Real.zero_le_six'
        exact
          Eq.subst
            (motive := fun x : ℝ => (6 : ℝ) ≤ x)
            Real.six_add_six_eq_twelve
            hsix_le_six_add_six
      have hcoeff :
          3 * (2 * max w.re |w.im - t|) =
            6 * max w.re |w.im - t| := by
        calc
          3 * (2 * max w.re |w.im - t|) =
              (3 * 2) * max w.re |w.im - t| := by
            exact (mul_assoc (3 : ℝ) 2 (max w.re |w.im - t|)).symm
          _ = 6 * max w.re |w.im - t| := by
            exact congrArg (fun c : ℝ => c * max w.re |w.im - t|)
              Real.three_mul_two_eq_six
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ 12 * max w.re |w.im - t|)
          hcoeff.symm
          (mul_le_mul_of_nonneg_right hsix_le_twelve hmax_nonneg)
    exact le_trans hthree_mul htwo_to_twelve
  have harg_le :
      (3 * ‖w‖) / max w.re |w.im - t| ≤ 12 := by
    exact
      (div_le_iff₀ hmax_pos).mpr hthreeN_le_twelve_max
  have harg_pos :
      0 < (3 * ‖w‖) / max w.re |w.im - t| :=
    div_pos (mul_pos Real.zero_lt_three hN_pos) hmax_pos
  exact Real.log_le_log harg_pos harg_le

/-- Integrated constant-log comparison on the nonpositive-center lower side of
the denominator branch wall. -/
theorem Complex.binetSecondFormula_minusMovingLog_integral_le_log_twelve_of_im_nonpos
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_im_nonpos : w.im ≤ 0) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log 12) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let F : ℝ → ℝ := fun t : ℝ =>
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 * Real.log 12) / Real.exp ((2 : ℝ) * Real.pi * t)
  have hF_integrable : IntegrableOn F S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let B : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / B t
    let Fcc : ℝ → ℝ := fun t : ℝ =>
      (2 * Real.log (A t)) / Real.exp ((2 : ℝ) * Real.pi * t)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hB_pos : ∀ t : ℝ, 0 < B t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hA_pos : ∀ t : ℝ, 0 < A t := by
      intro t
      exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hB_pos t)
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hB_cont : Continuous B :=
      continuous_const.sup hdist_cont
    have hA_cont : Continuous A :=
      continuous_const.div hB_cont (fun t => (hB_pos t).ne')
    have hlog_contOn :
        ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
      (hA_cont.continuousOn).log (fun t _ht => (hA_pos t).ne')
    have hnum_contOn :
        ContinuousOn (fun t : ℝ => 2 * Real.log (A t)) Scc :=
      continuousOn_const.mul hlog_contOn
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne :
        ∀ t : ℝ, t ∈ Scc →
          Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hFcc_contOn : ContinuousOn Fcc Scc :=
      hnum_contOn.div hden_cont.continuousOn hden_ne
    have hFcc_integrable : IntegrableOn Fcc Scc :=
      hFcc_contOn.integrableOn_Icc
    exact hFcc_integrable.mono_set Set.Ioc_subset_Icc_self
  have hG_integrable : IntegrableOn G S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let Gcc : ℝ → ℝ := fun t : ℝ =>
      (2 * Real.log 12) / Real.exp ((2 : ℝ) * Real.pi * t)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne :
        ∀ t : ℝ, t ∈ Scc →
          Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hGcc_contOn : ContinuousOn Gcc Scc :=
      continuousOn_const.div hden_cont.continuousOn hden_ne
    have hGcc_integrable : IntegrableOn Gcc Scc :=
      hGcc_contOn.integrableOn_Icc
    exact hGcc_integrable.mono_set Set.Ioc_subset_Icc_self
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, F t ≤ G t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht =>
        have hlog_le :
            Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
              Real.log 12 :=
          Complex.binetSecondFormula_minusMovingLog_le_log_twelve_of_im_nonpos
            hw_re_pos hw_im_nonpos (le_of_lt ht.1)
        have hnum_le :
            2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
              2 * Real.log 12 :=
          mul_le_mul_of_nonneg_left hlog_le zero_le_two
        have hden_nonneg :
            0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) :=
          le_of_lt (Real.exp_pos ((2 : ℝ) * Real.pi * t))
        div_le_div_of_nonneg_right hnum_le hden_nonneg)
  exact setIntegral_mono_ae_restrict hF_integrable hG_integrable hpoint

/-- A constant pure-exponential integral over the bounded Binet tail window has
the left-endpoint exponential scale. -/
theorem Complex.binetSecondFormula_constant_expWeighted_integral_le_expScale
    (K : ℝ)
    (hK_nonneg : 0 ≤ K)
    (w : ℂ) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        K / Real.exp ((2 : ℝ) * Real.pi * t) ≤
      K * Real.exp (-Real.pi * ‖w‖) := by
  let N : ℝ := ‖w‖
  let F : ℝ → ℝ := fun t : ℝ =>
    Real.exp (-((2 : ℝ) * Real.pi) * t)
  have htail_integrable :
      IntegrableOn F (Set.Ioi (N / 2)) := by
    have hcoeff_pos : 0 < (2 : ℝ) * Real.pi :=
      mul_pos two_pos Real.pi_pos
    exact exp_neg_integrableOn_Ioi (N / 2) hcoeff_pos
  have htail_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (N / 2))] F :=
    Filter.Eventually.of_forall
      (fun t => le_of_lt (Real.exp_pos (-((2 : ℝ) * Real.pi) * t)))
  have hsubset :
      Set.Ioc (N / 2) (2 * N) ≤ᵐ[volume] Set.Ioi (N / 2) :=
    Filter.Eventually.of_forall
      (fun t ht => ht.1)
  have hmono :
      ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t ≤
        ∫ t : ℝ in Set.Ioi (N / 2), F t :=
    setIntegral_mono_set htail_integrable htail_nonneg hsubset
  have htail_bound :
      ∫ t : ℝ in Set.Ioi (N / 2), F t ≤
        Real.exp (-((2 : ℝ) * Real.pi) * (N / 2)) :=
    Real.exp_neg_two_pi_tail_integral_le_exp (N / 2)
  have hexponent :
      -((2 : ℝ) * Real.pi) * (N / 2) = -Real.pi * ‖w‖ := by
    calc
      -((2 : ℝ) * Real.pi) * (N / 2) =
          -(((2 : ℝ) * Real.pi) * (N / 2)) := by
        exact neg_mul ((2 : ℝ) * Real.pi) (N / 2)
      _ = -(Real.pi * ‖w‖) := by
        have hinside :
            ((2 : ℝ) * Real.pi) * (N / 2) =
              Real.pi * ‖w‖ := by
          calc
            ((2 : ℝ) * Real.pi) * (N / 2) =
                ((2 : ℝ) * Real.pi) * (‖w‖ / 2) := by
              rfl
            _ = (((2 : ℝ) * Real.pi) * ‖w‖) / 2 := by
              exact (mul_div_assoc ((2 : ℝ) * Real.pi) ‖w‖ 2).symm
            _ = ((Real.pi * ‖w‖) * 2) / 2 := by
              exact
                congrArg (fun x : ℝ => x / 2)
                  (calc
                    ((2 : ℝ) * Real.pi) * ‖w‖ =
                        2 * (Real.pi * ‖w‖) := by
                      exact mul_assoc 2 Real.pi ‖w‖
                    _ = (Real.pi * ‖w‖) * 2 := by
                      exact mul_comm 2 (Real.pi * ‖w‖))
            _ = Real.pi * ‖w‖ := by
              exact mul_div_cancel_right₀ (Real.pi * ‖w‖) two_ne_zero
        exact congrArg Neg.neg hinside
      _ = -Real.pi * ‖w‖ := by
        exact (neg_mul Real.pi ‖w‖).symm
  have htail_scale :
      ∫ t : ℝ in Set.Ioi (N / 2), F t ≤
        Real.exp (-Real.pi * ‖w‖) :=
    Eq.subst
      (motive := fun x : ℝ =>
        ∫ t : ℝ in Set.Ioi (N / 2), F t ≤ Real.exp x)
      hexponent
      htail_bound
  have hscaled :
      K * (∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t) ≤
        K * Real.exp (-Real.pi * ‖w‖) :=
    le_trans
      (mul_le_mul_of_nonneg_left hmono hK_nonneg)
      (mul_le_mul_of_nonneg_left htail_scale hK_nonneg)
  have hintegrand_eq :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          K / Real.exp ((2 : ℝ) * Real.pi * t) =
        K * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t := by
    calc
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          K / Real.exp ((2 : ℝ) * Real.pi * t) =
          ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), K * F t := by
        exact
          setIntegral_congr_fun measurableSet_Ioc
            (fun t _ht =>
              calc
                K / Real.exp ((2 : ℝ) * Real.pi * t) =
                    K * (Real.exp ((2 : ℝ) * Real.pi * t))⁻¹ := by
                  rfl
                _ = K * Real.exp (-(((2 : ℝ) * Real.pi) * t)) := by
                  exact congrArg (fun x : ℝ => K * x)
                    (Real.exp_neg (((2 : ℝ) * Real.pi) * t)).symm
                _ = K * F t := by
                  exact congrArg (fun x : ℝ => K * Real.exp x)
                    (neg_mul ((2 : ℝ) * Real.pi) t).symm)
      _ = K * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t := by
        exact integral_mul_left K F
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤ K * Real.exp (-Real.pi * ‖w‖))
      hintegrand_eq.symm
      hscaled

end

end LFunctions
end Boundary
