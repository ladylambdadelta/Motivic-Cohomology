import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.RealPhaseBasics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Rat.Cast.Order

/-!
# Logarithmic phase estimates

This file owns the oscillatory phase `n^{-it}` input used by the
Euler-Maclaurin boundary argument.  The phase is logarithmic, not a
constant-ratio geometric progression.
-/

namespace Boundary
namespace LFunctions

noncomputable section
/-- Numerical lower bound used to show `log (2+N)` is uniformly positive. -/
theorem Complex.real_exp_half_le_two :
    Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have hexp_one_le_four : Real.exp (1 : ℝ) ≤ 4 :=
    le_trans
      (le_of_lt Real.exp_one_lt_d9)
      (le_of_lt real_decimal_exp_upper_lt_four_for_logarithmicPhase)
  have hsqrt_le_two : Real.sqrt (Real.exp (1 : ℝ)) ≤ 2 :=
    (Real.sqrt_le_left zero_le_two).mpr
      (by
        calc
          Real.exp (1 : ℝ) ≤ 4 := hexp_one_le_four
          _ = (2 : ℝ) ^ 2 := real_four_eq_two_sq_for_logarithmicPhase)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 2)
      (Real.exp_half (1 : ℝ)).symm
      hsqrt_le_two

/-- The standard logarithmic factor is bounded below uniformly on natural
cutoffs. -/
theorem Complex.logarithmicPhase_standardLog_half_le
    (N : ℕ) :
    (1 / 2 : ℝ) ≤ Real.log (2 + N) := by
  have hpos : 0 < (2 : ℝ) + N :=
    lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right (Nat.cast_nonneg N))
  have hexp_le : Real.exp (1 / 2 : ℝ) ≤ (2 : ℝ) + N :=
    le_trans Complex.real_exp_half_le_two
      (le_add_of_nonneg_right (Nat.cast_nonneg N))
  exact (Real.le_log_iff_exp_le hpos).mpr hexp_le

/-- Absorb the successor in the dyadic logarithm by multiplying the argument
by the base. -/
theorem Complex.nat_log2_add_one_eq_nat_log_two_mul_succ
    (N : ℕ) :
    Nat.log2 (N + 1) + 1 = Nat.log 2 ((N + 1) * 2) := by
  calc
    Nat.log2 (N + 1) + 1 = Nat.log 2 (N + 1) + 1 := by
      exact congrArg (fun k : ℕ => k + 1) Nat.log2_eq_log_two
    _ = Nat.log 2 ((N + 1) * 2) := by
      exact (Nat.log_mul_base Nat.one_lt_two (Nat.succ_ne_zero N)).symm

/-- Positivity of the natural logarithm of the dyadic base. -/
theorem Complex.real_log_two_pos :
    0 < Real.log (2 : ℝ) := by
  exact Real.log_pos one_lt_two

/-- Upper numerical bound for `log 2`. -/
theorem Complex.real_log_two_le_one :
    Real.log (2 : ℝ) ≤ 1 := by
  have htwo_pos : (0 : ℝ) < 2 :=
    zero_lt_two
  have htwo_le_exp : (2 : ℝ) ≤ Real.exp (1 : ℝ) :=
    le_of_lt
      (lt_trans real_two_lt_decimal_exp_lower_for_logarithmicPhase
        Real.exp_one_gt_d9)
  exact (Real.log_le_iff_le_exp htwo_pos).mpr htwo_le_exp

/-- Lower numerical bound for `log 2`. -/
theorem Complex.one_half_le_real_log_two :
    (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
  have hraw :
      (1 / 2 : ℝ) ≤ Real.log (2 + (0 : ℕ)) :=
    Complex.logarithmicPhase_standardLog_half_le 0
  have harg :
      (2 : ℝ) + (0 : ℕ) = 2 :=
    Eq.trans
      (congrArg (fun r : ℝ => (2 : ℝ) + r) Nat.cast_zero)
      (add_zero 2)
  exact Eq.subst
    (motive := fun r : ℝ => (1 / 2 : ℝ) ≤ Real.log r)
    harg
    hraw

/-- Strict lower numerical bound for `log 2`. -/
theorem Complex.one_half_lt_real_log_two :
    (1 / 2 : ℝ) < Real.log (2 : ℝ) := by
  have hexp_one_lt_four : Real.exp (1 : ℝ) < 4 :=
    lt_trans Real.exp_one_lt_d9 real_decimal_exp_upper_lt_four_for_logarithmicPhase
  have hexp_half_lt_two : Real.exp (1 / 2 : ℝ) < 2 := by
    have hsqrt : Real.sqrt (Real.exp (1 : ℝ)) < 2 :=
      (Real.sqrt_lt' zero_lt_two).mpr
        (by
          calc
            Real.exp (1 : ℝ) < 4 := hexp_one_lt_four
            _ = (2 : ℝ) ^ 2 := real_four_eq_two_sq_for_logarithmicPhase)
    exact Eq.subst
      (motive := fun y : ℝ => y < 2)
      (Real.exp_half (1 : ℝ)).symm
      hsqrt
  have htwo_pos : (0 : ℝ) < 2 :=
    zero_lt_two
  exact (Real.lt_log_iff_exp_lt htwo_pos).mpr hexp_half_lt_two

/-- The normalization identity for the lower logarithmic checkpoint. -/
theorem Real.two_mul_one_div_two_eq_one_for_logarithmicPhase :
    (2 : ℝ) * (1 / 2 : ℝ) = 1 := by
  exact mul_one_div_cancel (show (2 : ℝ) ≠ 0 from two_ne_zero)

/-- Rational arithmetic used to rescale the `2 / 3` logarithmic checkpoint. -/
theorem Real.two_mul_two_div_three_eq_four_div_three_for_logarithmicPhase :
    (2 : ℝ) * (2 / 3 : ℝ) = 4 / 3 := by
  calc
    (2 : ℝ) * (2 / 3 : ℝ) = 2 * (2 * 3⁻¹) := by
      exact congrArg (fun r : ℝ => (2 : ℝ) * r) (div_eq_mul_inv 2 3)
    _ = (2 * 2 : ℝ) * 3⁻¹ :=
      (mul_assoc (2 : ℝ) 2 3⁻¹).symm
    _ = (4 : ℝ) * 3⁻¹ := by
      exact congrArg
        (fun r : ℝ => r * 3⁻¹)
        ((two_mul (2 : ℝ)).trans two_add_two_eq_four)
    _ = 4 / 3 :=
      (div_eq_mul_inv 4 3).symm

/-- Local owner wrapper for the derivative of `x log x`. -/
theorem Real.hasDerivAt_id_mul_log_for_logarithmicPhase
    {x : ℝ}
    (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log x + 1) x := by
  exact Real.hasDerivAt_mul_log hx

/-- A rational lower bound for `log 2` used at the dyadic entropy checkpoint. -/
theorem Complex.two_thirds_le_real_log_two :
    (2 / 3 : ℝ) ≤ Real.log (2 : ℝ) := by
  have hexp_two_le_eight : Real.exp (2 : ℝ) ≤ 8 := by
    have hsq :
        Real.exp (2 : ℝ) = Real.exp (1 : ℝ) ^ 2 := by
      calc
        Real.exp (2 : ℝ) = Real.exp ((2 : ℕ) * (1 : ℝ)) :=
          real_exp_two_eq_exp_nat_two_mul_one_for_logarithmicPhase
        _ = Real.exp (1 : ℝ) ^ 2 :=
          Real.exp_nat_mul (1 : ℝ) 2
    have hsq_bound : Real.exp (1 : ℝ) ^ 2 < (8 : ℝ) := by
      calc
        Real.exp (1 : ℝ) ^ 2 < (2.7182818286 : ℝ) ^ 2 := by
          exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le
            (show (2 : ℕ) ≠ 0 from Nat.succ_ne_zero 1)
        _ < (8 : ℝ) := real_decimal_exp_upper_sq_lt_eight_for_logarithmicPhase
    exact le_of_lt (Eq.subst (motive := fun z : ℝ => z < 8) hsq.symm hsq_bound)
  have hlog_eight : (2 : ℝ) ≤ Real.log (8 : ℝ) :=
    (Real.le_log_iff_exp_le real_zero_lt_eight_for_logarithmicPhase).mpr
      hexp_two_le_eight
  have hlog_pow :
      Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
    calc
      Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ 3) :=
        congrArg Real.log real_eight_eq_two_pow_three_for_logarithmicPhase
      _ = (3 : ℝ) * Real.log (2 : ℝ) :=
        Real.log_pow (2 : ℝ) 3
  have htwo_le_three_log : (2 : ℝ) ≤ 3 * Real.log (2 : ℝ) :=
    Eq.subst (motive := fun target : ℝ => (2 : ℝ) ≤ target) hlog_pow hlog_eight
  have hthird_nonneg : 0 ≤ (3 : ℝ)⁻¹ :=
    inv_nonneg.mpr zero_lt_three.le
  have hscaled :
      (3 : ℝ)⁻¹ * 2 ≤ (3 : ℝ)⁻¹ * (3 * Real.log (2 : ℝ)) :=
    mul_le_mul_of_nonneg_left htwo_le_three_log hthird_nonneg
  have hleft :
      (3 : ℝ)⁻¹ * 2 = 2 / 3 :=
    inv_mul_eq_div 3 2
  have hright :
      (3 : ℝ)⁻¹ * (3 * Real.log (2 : ℝ)) = Real.log (2 : ℝ) := by
    calc
      (3 : ℝ)⁻¹ * (3 * Real.log (2 : ℝ)) =
          ((3 : ℝ)⁻¹ * 3) * Real.log (2 : ℝ) :=
        (mul_assoc (3 : ℝ)⁻¹ 3 (Real.log (2 : ℝ))).symm
      _ = 1 * Real.log (2 : ℝ) :=
        congrArg (fun r : ℝ => r * Real.log (2 : ℝ))
          (show (3 : ℝ)⁻¹ * 3 = 1 from
            inv_mul_cancel₀ (show (3 : ℝ) ≠ 0 from ne_of_gt zero_lt_three))
      _ = Real.log (2 : ℝ) :=
        one_mul (Real.log (2 : ℝ))
  exact Eq.subst
    (motive := fun left : ℝ => left ≤ Real.log (2 : ℝ))
    hleft
    (Eq.subst
      (motive := fun right : ℝ => (3 : ℝ)⁻¹ * 2 ≤ right)
      hright
      hscaled)

/-- The denominator in the explicit critical point is nonnegative. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_den_nonneg :
    0 ≤ 2 * Real.log (2 : ℝ) - 1 := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) :=
    Complex.one_half_le_real_log_two
  have htwice : (1 : ℝ) ≤ 2 * Real.log (2 : ℝ) := by
    have hscaled :
        2 * (1 / 2 : ℝ) ≤ 2 * Real.log (2 : ℝ) :=
      mul_le_mul_of_nonneg_left hhalf zero_lt_two.le
    have hleft : 2 * (1 / 2 : ℝ) = 1 :=
      Real.two_mul_one_div_two_eq_one_for_logarithmicPhase
    exact Eq.subst
      (motive := fun left : ℝ => left ≤ 2 * Real.log (2 : ℝ))
      hleft
      hscaled
  exact sub_nonneg.mpr htwice

/-- Strict lower bound for the critical-point denominator. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_den_pos :
    0 < 2 * Real.log (2 : ℝ) - 1 := by
  have hhalf : (1 / 2 : ℝ) < Real.log (2 : ℝ) :=
    Complex.one_half_lt_real_log_two
  have htwice : (1 : ℝ) < 2 * Real.log (2 : ℝ) := by
    exact (div_lt_iff₀' zero_lt_two).mp hhalf
  exact sub_pos.mpr htwice

/-- The numerator in the explicit critical point is nonnegative. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_num_nonneg :
    0 ≤ 2 - 2 * Real.log (2 : ℝ) := by
  have hlog_le_one : Real.log (2 : ℝ) ≤ 1 :=
    Complex.real_log_two_le_one
  have htwice : 2 * Real.log (2 : ℝ) ≤ (2 : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left hlog_le_one zero_le_two
  have htwice' : 2 * Real.log (2 : ℝ) ≤ 2 := by
    exact Eq.subst (motive := fun rhs : ℝ => 2 * Real.log (2 : ℝ) ≤ rhs) (mul_one 2) htwice
  exact sub_nonneg.mpr htwice'

/-- Defect function for the sharp dyadic-log comparison.  The target inequality
is exactly nonnegativity of this function on `[0,∞)`. -/
def Complex.realLogDyadicComparisonDefect
    (x : ℝ) : ℝ :=
  (2 * Real.log (x + 2)) * Real.log (2 : ℝ) -
    Real.log (2 * (x + 1))

/-- Critical point of the dyadic-log comparison defect. -/
def Complex.realLogDyadicComparisonCriticalPoint : ℝ :=
  (2 - 2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1)

/-- The dyadic-log comparison critical point lies in the nonnegative interval. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_nonneg :
    0 ≤ Complex.realLogDyadicComparisonCriticalPoint := by
  exact div_nonneg
    Complex.realLogDyadicComparisonCriticalPoint_num_nonneg
    Complex.realLogDyadicComparisonCriticalPoint_den_nonneg

/-- Elementary cancellation used in the derivative of `log (2 * (x + 1))`. -/
theorem Complex.two_div_two_mul_eq_one_div
    {u : ℝ} :
    (2 : ℝ) / (2 * u) = 1 / u := by
  calc
    (2 : ℝ) / (2 * u) = (2 : ℝ) * (2 * u)⁻¹ :=
      div_eq_mul_inv 2 (2 * u)
    _ = (2 : ℝ) * (u⁻¹ * (2 : ℝ)⁻¹) := by
      exact congrArg (fun z : ℝ => (2 : ℝ) * z) (mul_inv_rev 2 u)
    _ = ((2 : ℝ) * (2 : ℝ)⁻¹) * u⁻¹ := by
      exact real_two_mul_inv_mul_two_inv_reassociate_for_logarithmicPhase u
    _ = (1 : ℝ) * u⁻¹ := by
      exact congrArg (fun z : ℝ => z * u⁻¹) (mul_inv_cancel₀ two_ne_zero)
    _ = u⁻¹ :=
      one_mul u⁻¹
    _ = 1 / u :=
      (one_div u).symm

/-- Positive denominator for the dyadic defect derivative on `[0,∞)`. -/
theorem Complex.realLogDyadicComparisonDefect_deriv_den_pos
    {x : ℝ}
    (hx : 0 ≤ x) :
    0 < (x + 2) * (x + 1) := by
  have hx_two : 0 < x + 2 :=
    real_zero_lt_add_two_of_nonneg_for_logarithmicPhase hx
  have hx_one : 0 < x + 1 :=
    real_zero_lt_add_one_of_nonneg_for_logarithmicPhase hx
  exact mul_pos hx_two hx_one

/-- Exact factorization of the dyadic defect derivative around the critical
point. -/
theorem Complex.realLogDyadicComparisonDefect_deriv_factorization
    {x : ℝ}
    (hx : 0 ≤ x) :
    2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) =
      ((2 * Real.log (2 : ℝ) - 1) *
        (x - Complex.realLogDyadicComparisonCriticalPoint)) /
          ((x + 2) * (x + 1)) := by
  have hx_two_ne : x + 2 ≠ 0 :=
    ne_of_gt (real_zero_lt_add_two_of_nonneg_for_logarithmicPhase hx)
  have hx_one_ne : x + 1 ≠ 0 :=
    ne_of_gt (real_zero_lt_add_one_of_nonneg_for_logarithmicPhase hx)
  have hcrit_den_ne : 2 * Real.log (2 : ℝ) - 1 ≠ 0 :=
    ne_of_gt Complex.realLogDyadicComparisonCriticalPoint_den_pos
  unfold Complex.realLogDyadicComparisonCriticalPoint
  calc
    2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) =
        ((2 * Real.log (2 : ℝ)) * (x + 1) - 1 * (x + 2)) /
          ((x + 2) * (x + 1)) := by
      exact real_dyadic_deriv_left_common_denominator_for_logarithmicPhase
        (Real.log (2 : ℝ)) x hx_two_ne hx_one_ne
    _ =
        ((2 * Real.log (2 : ℝ) - 1) *
          (x - (2 - 2 * Real.log (2 : ℝ)) /
            (2 * Real.log (2 : ℝ) - 1))) /
          ((x + 2) * (x + 1)) := by
      exact congrArg
        (fun z : ℝ => z / ((x + 2) * (x + 1)))
        (real_dyadic_deriv_numerator_factor_for_logarithmicPhase
          (Real.log (2 : ℝ)) x hcrit_den_ne)

/-- Derivative formula for the dyadic-log comparison defect on `(0,∞)`. -/
theorem Complex.realLogDyadicComparisonDefect_hasDerivAt
    {x : ℝ}
    (hx : 0 ≤ x) :
    HasDerivAt
      Complex.realLogDyadicComparisonDefect
      (2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1))
      x := by
  have hx_two_pos : 0 < x + 2 :=
    real_zero_lt_add_two_of_nonneg_for_logarithmicPhase hx
  have hx_one_pos : 0 < x + 1 :=
    real_zero_lt_add_one_of_nonneg_for_logarithmicPhase hx
  have hlog_shift :
      HasDerivAt (fun y : ℝ => Real.log (y + 2)) (1 / (x + 2)) x := by
    have hshift : HasDerivAt (fun y : ℝ => y + 2) 1 x :=
      (hasDerivAt_id x).add_const 2
    have hne : x + 2 ≠ 0 :=
      ne_of_gt hx_two_pos
    exact hshift.log hne
  have hleft :
      HasDerivAt
        (fun y : ℝ => (2 * Real.log (y + 2)) * Real.log (2 : ℝ))
        (2 * Real.log (2 : ℝ) / (x + 2))
        x := by
    have hscaled :
        HasDerivAt
          (fun y : ℝ => (2 * Real.log (y + 2)) * Real.log (2 : ℝ))
          ((2 * (1 / (x + 2))) * Real.log (2 : ℝ))
          x :=
      (hlog_shift.const_mul 2).mul_const (Real.log (2 : ℝ))
    have hderiv :
        ((2 * (1 / (x + 2))) * Real.log (2 : ℝ)) =
          2 * Real.log (2 : ℝ) / (x + 2) := by
      exact real_two_one_div_mul_eq_two_mul_div_for_logarithmicPhase
        (Real.log (2 : ℝ)) (x + 2)
    exact Eq.subst
      (motive := fun d : ℝ =>
        HasDerivAt
          (fun y : ℝ => (2 * Real.log (y + 2)) * Real.log (2 : ℝ))
          d
          x)
      hderiv
      hscaled
  have hlog_linear :
      HasDerivAt (fun y : ℝ => Real.log (2 * (y + 1))) (1 / (x + 1)) x := by
    have hshift : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
      (hasDerivAt_id x).add_const 1
    have hlinear : HasDerivAt (fun y : ℝ => 2 * (y + 1)) 2 x := by
      have hscaled : HasDerivAt (fun y : ℝ => 2 * (y + 1)) (2 * 1) x :=
        hshift.const_mul 2
      exact Eq.subst
        (motive := fun d : ℝ => HasDerivAt (fun y : ℝ => 2 * (y + 1)) d x)
        (mul_one 2)
        hscaled
    have hne : 2 * (x + 1) ≠ 0 :=
      mul_ne_zero two_ne_zero (ne_of_gt hx_one_pos)
    have hlog : HasDerivAt (fun y : ℝ => Real.log (2 * (y + 1))) (2 / (2 * (x + 1))) x :=
      hlinear.log hne
    have hderiv : 2 / (2 * (x + 1)) = 1 / (x + 1) := by
      exact Complex.two_div_two_mul_eq_one_div
    exact Eq.subst
      (motive := fun d : ℝ =>
        HasDerivAt (fun y : ℝ => Real.log (2 * (y + 1))) d x)
      hderiv
      hlog
  have hsub :
      HasDerivAt
        (fun y : ℝ =>
          (2 * Real.log (y + 2)) * Real.log (2 : ℝ) -
            Real.log (2 * (y + 1)))
        (2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1))
        x :=
    hleft.sub hlog_linear
  exact hsub

/-- Algebraic sign of the dyadic defect derivative before the critical point. -/
theorem Complex.realLogDyadicComparisonDefect_deriv_nonpos_on_left
    {x : ℝ}
    (hx : x ∈ Set.Icc 0 Complex.realLogDyadicComparisonCriticalPoint) :
    2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) ≤ 0 := by
  have hfactor :
      2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) =
        ((2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint)) /
            ((x + 2) * (x + 1)) :=
    Complex.realLogDyadicComparisonDefect_deriv_factorization hx.1
  have hnum_nonpos :
      (2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint) ≤ 0 := by
    have hden_nonneg : 0 ≤ 2 * Real.log (2 : ℝ) - 1 :=
      le_of_lt Complex.realLogDyadicComparisonCriticalPoint_den_pos
    have hdiff_nonpos : x - Complex.realLogDyadicComparisonCriticalPoint ≤ 0 :=
      sub_nonpos.mpr hx.2
    exact mul_nonpos_of_nonneg_of_nonpos hden_nonneg hdiff_nonpos
  have hden_pos : 0 < (x + 2) * (x + 1) :=
    Complex.realLogDyadicComparisonDefect_deriv_den_pos hx.1
  have hquot_nonpos :
      ((2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint)) /
            ((x + 2) * (x + 1)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_pos.le
  exact Eq.subst (motive := fun d : ℝ => d ≤ 0) hfactor.symm hquot_nonpos

/-- Algebraic sign of the dyadic defect derivative after the critical point. -/
theorem Complex.realLogDyadicComparisonDefect_deriv_nonneg_on_right
    {x : ℝ}
    (hx : x ∈ Set.Ici Complex.realLogDyadicComparisonCriticalPoint) :
    0 ≤ 2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) := by
  have hx_nonneg : 0 ≤ x :=
    le_trans Complex.realLogDyadicComparisonCriticalPoint_nonneg hx
  have hfactor :
      2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) =
        ((2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint)) /
            ((x + 2) * (x + 1)) :=
    Complex.realLogDyadicComparisonDefect_deriv_factorization hx_nonneg
  have hnum_nonneg :
      0 ≤
        (2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint) := by
    have hden_nonneg : 0 ≤ 2 * Real.log (2 : ℝ) - 1 :=
      le_of_lt Complex.realLogDyadicComparisonCriticalPoint_den_pos
    have hdiff_nonneg : 0 ≤ x - Complex.realLogDyadicComparisonCriticalPoint :=
      sub_nonneg.mpr hx
    exact mul_nonneg hden_nonneg hdiff_nonneg
  have hden_pos : 0 < (x + 2) * (x + 1) :=
    Complex.realLogDyadicComparisonDefect_deriv_den_pos hx_nonneg
  have hquot_nonneg :
      0 ≤
        ((2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint)) /
            ((x + 2) * (x + 1)) :=
    div_nonneg hnum_nonneg hden_pos.le
  exact Eq.subst (motive := fun d : ℝ => 0 ≤ d) hfactor.symm hquot_nonneg

/-- The dyadic-log comparison defect is antitone until its critical point. -/
theorem Complex.realLogDyadicComparisonDefect_antitoneOn_left :
    AntitoneOn
      Complex.realLogDyadicComparisonDefect
      (Set.Icc 0 Complex.realLogDyadicComparisonCriticalPoint) := by
  exact
    antitoneOn_of_deriv_nonpos
      (convex_Icc 0 Complex.realLogDyadicComparisonCriticalPoint)
      (fun x hx =>
        (Complex.realLogDyadicComparisonDefect_hasDerivAt
          hx.1).continuousAt.continuousWithinAt)
      (fun x hx =>
        have hx_closed :
            x ∈ Set.Icc 0 Complex.realLogDyadicComparisonCriticalPoint :=
          interior_subset hx
        (Complex.realLogDyadicComparisonDefect_hasDerivAt
          hx_closed.1).differentiableAt.differentiableWithinAt)
      (fun x hx =>
        have hx_closed :
            x ∈ Set.Icc 0 Complex.realLogDyadicComparisonCriticalPoint :=
          interior_subset hx
        Eq.subst
          (motive := fun d : ℝ => d ≤ 0)
          (Complex.realLogDyadicComparisonDefect_hasDerivAt hx_closed.1).deriv.symm
          (Complex.realLogDyadicComparisonDefect_deriv_nonpos_on_left hx_closed))

/-- The dyadic-log comparison defect is monotone after its critical point. -/
theorem Complex.realLogDyadicComparisonDefect_monotoneOn_right :
    MonotoneOn
      Complex.realLogDyadicComparisonDefect
      (Set.Ici Complex.realLogDyadicComparisonCriticalPoint) := by
  exact
    monotoneOn_of_deriv_nonneg
      (convex_Ici Complex.realLogDyadicComparisonCriticalPoint)
      (fun x hx =>
        (Complex.realLogDyadicComparisonDefect_hasDerivAt
          (le_trans Complex.realLogDyadicComparisonCriticalPoint_nonneg hx)).continuousAt.continuousWithinAt)
      (fun x hx =>
        have hx_closed :
            x ∈ Set.Ici Complex.realLogDyadicComparisonCriticalPoint :=
          interior_subset hx
        (Complex.realLogDyadicComparisonDefect_hasDerivAt
          (le_trans Complex.realLogDyadicComparisonCriticalPoint_nonneg hx_closed)).differentiableAt.differentiableWithinAt)
      (fun x hx =>
        have hx_closed :
            x ∈ Set.Ici Complex.realLogDyadicComparisonCriticalPoint :=
          interior_subset hx
        Eq.subst
          (motive := fun d : ℝ => 0 ≤ d)
          (Complex.realLogDyadicComparisonDefect_hasDerivAt
            (le_trans Complex.realLogDyadicComparisonCriticalPoint_nonneg hx_closed)).deriv.symm
          (Complex.realLogDyadicComparisonDefect_deriv_nonneg_on_right hx_closed))

/-- The endpoint value of the dyadic-log comparison defect is nonnegative. -/
theorem Complex.realLogDyadicComparisonDefect_zero_nonneg :
    0 ≤ Complex.realLogDyadicComparisonDefect 0 := by
  have hdef :
      Complex.realLogDyadicComparisonDefect 0 =
        (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
          Real.log (2 : ℝ) := by
    have harg_two : (0 : ℝ) + 2 = 2 :=
      real_zero_add_two_eq_two_for_logarithmicPhase
    have hmul : (2 : ℝ) * (0 + 1) = 2 :=
      real_two_mul_zero_add_one_eq_two_for_logarithmicPhase
    calc
      Complex.realLogDyadicComparisonDefect 0 =
          (2 * Real.log ((0 : ℝ) + 2)) * Real.log (2 : ℝ) -
            Real.log ((2 : ℝ) * (0 + 1)) := by
        rfl
      _ = (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
            Real.log ((2 : ℝ) * (0 + 1)) := by
        exact congrArg
          (fun z : ℝ => (2 * Real.log z) * Real.log (2 : ℝ) -
            Real.log ((2 : ℝ) * (0 + 1)))
          harg_two
      _ = (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
            Real.log (2 : ℝ) := by
        exact congrArg
          (fun z : ℝ => (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
            Real.log z)
          hmul
  have hlog_nonneg : 0 ≤ Real.log (2 : ℝ) :=
    le_of_lt Complex.real_log_two_pos
  have hfactor_nonneg : 0 ≤ 2 * Real.log (2 : ℝ) - 1 :=
    Complex.realLogDyadicComparisonCriticalPoint_den_nonneg
  have hprod :
      0 ≤ Real.log (2 : ℝ) * (2 * Real.log (2 : ℝ) - 1) :=
    mul_nonneg hlog_nonneg hfactor_nonneg
  have halg :
      (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
          Real.log (2 : ℝ) =
        Real.log (2 : ℝ) * (2 * Real.log (2 : ℝ) - 1) := by
    exact real_log_endpoint_factor_for_logarithmicPhase (Real.log (2 : ℝ))
  exact Eq.subst
    (motive := fun target : ℝ => 0 ≤ target)
    hdef.symm
    (Eq.subst (motive := fun target : ℝ => 0 ≤ target) halg.symm hprod)

/-- At the critical point, the shifted `x+1` denominator has this explicit
value. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_add_one_eq :
    Complex.realLogDyadicComparisonCriticalPoint + 1 =
      1 / (2 * Real.log (2 : ℝ) - 1) := by
  have hden_ne : 2 * Real.log (2 : ℝ) - 1 ≠ 0 :=
    ne_of_gt Complex.realLogDyadicComparisonCriticalPoint_den_pos
  unfold Complex.realLogDyadicComparisonCriticalPoint
  exact real_critical_fraction_add_one_for_logarithmicPhase
    (Real.log (2 : ℝ))
    hden_ne

/-- At the critical point, the shifted `x+2` denominator has this explicit
value. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_add_two_eq :
    Complex.realLogDyadicComparisonCriticalPoint + 2 =
      (2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1) := by
  have hden_ne : 2 * Real.log (2 : ℝ) - 1 ≠ 0 :=
    ne_of_gt Complex.realLogDyadicComparisonCriticalPoint_den_pos
  unfold Complex.realLogDyadicComparisonCriticalPoint
  exact real_critical_fraction_add_two_for_logarithmicPhase
    (Real.log (2 : ℝ))
    hden_ne

/-- Entropy-form expression behind the dyadic critical value. -/
def Complex.realLogDyadicEntropyExpression
    (y : ℝ) : ℝ :=
  y * Real.log y - (y - 1) * Real.log (y - 1)

/-- Derivative formula for the entropy-form expression. -/
theorem Complex.realLogDyadicEntropyExpression_hasDerivAt
    {y : ℝ}
    (hy : 1 < y) :
    HasDerivAt
      Complex.realLogDyadicEntropyExpression
      (Real.log y - Real.log (y - 1))
      y := by
  have hy_ne : y ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one hy)
  have hy_sub_pos : 0 < y - 1 :=
    sub_pos.mpr hy
  have hy_sub_ne : y - 1 ≠ 0 :=
    ne_of_gt hy_sub_pos
  have hleft :
      HasDerivAt (fun z : ℝ => z * Real.log z) (Real.log y + 1) y :=
    Real.hasDerivAt_id_mul_log_for_logarithmicPhase hy_ne
  have hshift : HasDerivAt (fun z : ℝ => z - 1) 1 y :=
    (hasDerivAt_id y).sub_const 1
  have hright :
      HasDerivAt
        (fun z : ℝ => (z - 1) * Real.log (z - 1))
        (Real.log (y - 1) + 1)
        y := by
    have hmul_log :
        HasDerivAt (fun u : ℝ => u * Real.log u)
          (Real.log (y - 1) + 1)
          (y - 1) :=
      Real.hasDerivAt_id_mul_log_for_logarithmicPhase hy_sub_ne
    have hcomp :
        HasDerivAt
          (fun z : ℝ => (fun u : ℝ => u * Real.log u) (z - 1))
          ((Real.log (y - 1) + 1) * 1)
          y :=
      hmul_log.comp y hshift
    exact Eq.subst
      (motive := fun d : ℝ =>
        HasDerivAt
          (fun z : ℝ => (z - 1) * Real.log (z - 1))
          d
          y)
      (mul_one (Real.log (y - 1) + 1))
      hcomp
  have hsub :
      HasDerivAt
        (fun z : ℝ => z * Real.log z - (z - 1) * Real.log (z - 1))
        ((Real.log y + 1) - (Real.log (y - 1) + 1))
        y :=
    hleft.sub hright
  have hderiv :
      (Real.log y + 1) - (Real.log (y - 1) + 1) =
        Real.log y - Real.log (y - 1) := by
    exact real_add_one_sub_add_one_eq_sub_for_logarithmicPhase
      (Real.log y)
      (Real.log (y - 1))
  exact Eq.subst
    (motive := fun d : ℝ =>
      HasDerivAt Complex.realLogDyadicEntropyExpression d y)
    hderiv
    hsub

/-- The entropy-form derivative is nonnegative on `(1,∞)`. -/
theorem Complex.realLogDyadicEntropyExpression_deriv_nonneg
    {y : ℝ}
    (hy : 1 < y) :
    0 ≤ Real.log y - Real.log (y - 1) := by
  have hy_sub_pos : 0 < y - 1 :=
    sub_pos.mpr hy
  have hsub_le_y : y - 1 ≤ y := by
    exact real_sub_one_le_self_for_logarithmicPhase y
  have hlog_le : Real.log (y - 1) ≤ Real.log y :=
    Real.log_le_log hy_sub_pos hsub_le_y
  exact sub_nonneg.mpr hlog_le

/-- The entropy-form expression is monotone on the interval actually used by
the critical-point argument. -/
theorem Complex.realLogDyadicEntropyExpression_monotoneOn_Ici_two_log :
    MonotoneOn
      Complex.realLogDyadicEntropyExpression
      (Set.Ici (2 * Real.log (2 : ℝ))) := by
  exact
    monotoneOn_of_deriv_nonneg
      (convex_Ici (2 * Real.log (2 : ℝ)))
      (fun y hy =>
        (Complex.realLogDyadicEntropyExpression_hasDerivAt
          (lt_of_lt_of_le
            (sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos)
            hy)).continuousAt.continuousWithinAt)
      (fun y hy =>
        have hy_closed : y ∈ Set.Ici (2 * Real.log (2 : ℝ)) :=
          interior_subset hy
        (Complex.realLogDyadicEntropyExpression_hasDerivAt
          (lt_of_lt_of_le
            (sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos)
            hy_closed)).differentiableAt.differentiableWithinAt)
      (fun y hy =>
        have hy_closed : y ∈ Set.Ici (2 * Real.log (2 : ℝ)) :=
          interior_subset hy
        Eq.subst
          (motive := fun d : ℝ => 0 ≤ d)
          (Complex.realLogDyadicEntropyExpression_hasDerivAt
            (lt_of_lt_of_le
              (sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos)
              hy_closed)).deriv.symm
          (Complex.realLogDyadicEntropyExpression_deriv_nonneg
            (lt_of_lt_of_le
              (sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos)
              hy_closed)))

/-- The entropy-form expression is monotone on any interval `[a,∞)` with
`1 < a`. -/
theorem Complex.realLogDyadicEntropyExpression_monotoneOn_Ici_of_one_lt
    {a : ℝ}
    (ha : 1 < a) :
    MonotoneOn Complex.realLogDyadicEntropyExpression (Set.Ici a) := by
  exact
    monotoneOn_of_deriv_nonneg
      (convex_Ici a)
      (fun y hy =>
        (Complex.realLogDyadicEntropyExpression_hasDerivAt
          (lt_of_lt_of_le ha hy)).continuousAt.continuousWithinAt)
      (fun y hy =>
        have hy_closed : y ∈ Set.Ici a :=
          interior_subset hy
        (Complex.realLogDyadicEntropyExpression_hasDerivAt
          (lt_of_lt_of_le ha hy_closed)).differentiableAt.differentiableWithinAt)
      (fun y hy =>
        have hy_closed : y ∈ Set.Ici a :=
          interior_subset hy
        Eq.subst
          (motive := fun d : ℝ => 0 ≤ d)
          (Complex.realLogDyadicEntropyExpression_hasDerivAt
            (lt_of_lt_of_le ha hy_closed)).deriv.symm
          (Complex.realLogDyadicEntropyExpression_deriv_nonneg
            (lt_of_lt_of_le ha hy_closed)))

/-- Rational checkpoint for the entropy-form expression. -/
theorem Complex.real_log_two_le_entropyExpression_at_four_thirds :
    Real.log (2 : ℝ) ≤
      Complex.realLogDyadicEntropyExpression (4 / 3 : ℝ) := by
  have hlog_three_le :
      Real.log (3 : ℝ) ≤ (5 / 3 : ℝ) * Real.log (2 : ℝ) := by
    have hlog_27_le_32 : Real.log (27 : ℝ) ≤ Real.log (32 : ℝ) :=
      Real.log_le_log
        real_zero_lt_twenty_seven_for_logarithmicPhase
        real_twenty_seven_le_thirty_two_for_logarithmicPhase
    have hlog_27 : Real.log (27 : ℝ) = (3 : ℝ) * Real.log (3 : ℝ) := by
      calc
        Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) :=
          congrArg Real.log real_twenty_seven_eq_three_pow_three_for_logarithmicPhase
        _ = (3 : ℝ) * Real.log (3 : ℝ) :=
          Real.log_pow (3 : ℝ) 3
    have hlog_32 : Real.log (32 : ℝ) = (5 : ℝ) * Real.log (2 : ℝ) := by
      calc
        Real.log (32 : ℝ) = Real.log ((2 : ℝ) ^ 5) :=
          congrArg Real.log real_thirty_two_eq_two_pow_five_for_logarithmicPhase
        _ = (5 : ℝ) * Real.log (2 : ℝ) :=
          Real.log_pow (2 : ℝ) 5
    have hthree :
        (3 : ℝ) * Real.log (3 : ℝ) ≤ (5 : ℝ) * Real.log (2 : ℝ) :=
      Eq.subst
        (motive := fun lhs : ℝ => lhs ≤ (5 : ℝ) * Real.log (2 : ℝ))
        hlog_27
        (Eq.subst
          (motive := fun rhs : ℝ => Real.log (27 : ℝ) ≤ rhs)
          hlog_32
          hlog_27_le_32)
    have hthird_nonneg : 0 ≤ (3 : ℝ)⁻¹ :=
      inv_nonneg.mpr zero_lt_three.le
    have hscaled :
        (3 : ℝ)⁻¹ * ((3 : ℝ) * Real.log (3 : ℝ)) ≤
          (3 : ℝ)⁻¹ * ((5 : ℝ) * Real.log (2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hthree hthird_nonneg
    have hleft :
        (3 : ℝ)⁻¹ * ((3 : ℝ) * Real.log (3 : ℝ)) =
          Real.log (3 : ℝ) := by
      calc
        (3 : ℝ)⁻¹ * ((3 : ℝ) * Real.log (3 : ℝ)) =
            ((3 : ℝ)⁻¹ * 3) * Real.log (3 : ℝ) :=
          (mul_assoc (3 : ℝ)⁻¹ 3 (Real.log (3 : ℝ))).symm
        _ = 1 * Real.log (3 : ℝ) :=
          congrArg (fun r : ℝ => r * Real.log (3 : ℝ))
            (show (3 : ℝ)⁻¹ * 3 = 1 from
              inv_mul_cancel₀ (show (3 : ℝ) ≠ 0 from ne_of_gt zero_lt_three))
        _ = Real.log (3 : ℝ) :=
          one_mul (Real.log (3 : ℝ))
    have hright :
        (3 : ℝ)⁻¹ * ((5 : ℝ) * Real.log (2 : ℝ)) =
          (5 / 3 : ℝ) * Real.log (2 : ℝ) := by
      calc
        (3 : ℝ)⁻¹ * ((5 : ℝ) * Real.log (2 : ℝ)) =
            ((3 : ℝ)⁻¹ * 5) * Real.log (2 : ℝ) :=
          (mul_assoc (3 : ℝ)⁻¹ 5 (Real.log (2 : ℝ))).symm
        _ = (5 / 3 : ℝ) * Real.log (2 : ℝ) :=
          congrArg (fun r : ℝ => r * Real.log (2 : ℝ)) (inv_mul_eq_div 3 5)
    exact Eq.subst
      (motive := fun left : ℝ => left ≤ (5 / 3 : ℝ) * Real.log (2 : ℝ))
      hleft
      (Eq.subst
        (motive := fun right : ℝ =>
          (3 : ℝ)⁻¹ * ((3 : ℝ) * Real.log (3 : ℝ)) ≤ right)
        hright
        hscaled)
  have hvalue :
      Complex.realLogDyadicEntropyExpression (4 / 3 : ℝ) =
        (8 / 3 : ℝ) * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
    have hfour_ne : (4 / 3 : ℝ) ≠ 0 :=
      real_four_div_three_ne_zero_for_logarithmicPhase
    have hone_ne : ((4 / 3 : ℝ) - 1) ≠ 0 :=
      real_four_div_three_sub_one_ne_zero_for_logarithmicPhase
    have hlog_four_thirds :
        Real.log (4 / 3 : ℝ) = 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
      calc
        Real.log (4 / 3 : ℝ) = Real.log ((4 : ℝ) / 3) := rfl
        _ = Real.log (4 : ℝ) - Real.log (3 : ℝ) :=
          Real.log_div (ne_of_gt zero_lt_four) (ne_of_gt zero_lt_three)
        _ = 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
          have hlog_four : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
            calc
              Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) :=
                congrArg Real.log real_four_eq_two_sq_for_logarithmicPhase
              _ = (2 : ℝ) * Real.log (2 : ℝ) :=
                Real.log_pow (2 : ℝ) 2
          exact congrArg (fun z : ℝ => z - Real.log (3 : ℝ)) hlog_four
    have hlog_one_third :
        Real.log ((4 / 3 : ℝ) - 1) = - Real.log (3 : ℝ) := by
      calc
        Real.log ((4 / 3 : ℝ) - 1) = Real.log ((1 : ℝ) / 3) :=
          congrArg Real.log real_four_div_three_sub_one_eq_one_div_three_for_logarithmicPhase
        _ = Real.log (1 : ℝ) - Real.log (3 : ℝ) :=
          Real.log_div one_ne_zero (ne_of_gt zero_lt_three)
        _ = - Real.log (3 : ℝ) := by
          exact real_log_one_sub_log_eq_neg_log_for_logarithmicPhase 3
    calc
      Complex.realLogDyadicEntropyExpression (4 / 3 : ℝ) =
          (4 / 3 : ℝ) * Real.log (4 / 3 : ℝ) -
            ((4 / 3 : ℝ) - 1) * Real.log ((4 / 3 : ℝ) - 1) := by
        rfl
      _ = (4 / 3 : ℝ) * (2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) -
            ((4 / 3 : ℝ) - 1) * (- Real.log (3 : ℝ)) := by
        exact congrArg₂ Sub.sub
          (congrArg (fun z : ℝ => (4 / 3 : ℝ) * z) hlog_four_thirds)
          (congrArg (fun z : ℝ => ((4 / 3 : ℝ) - 1) * z) hlog_one_third)
      _ = (8 / 3 : ℝ) * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
        exact real_four_thirds_entropy_value_algebra_for_logarithmicPhase
          (Real.log (2 : ℝ)) (Real.log (3 : ℝ))
  have htarget :
      Real.log (2 : ℝ) ≤ (8 / 3 : ℝ) * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
    have hmove :
        Real.log (2 : ℝ) + Real.log (3 : ℝ) ≤
          (8 / 3 : ℝ) * Real.log (2 : ℝ) := by
      have hsum :
          Real.log (2 : ℝ) + Real.log (3 : ℝ) ≤
            Real.log (2 : ℝ) + (5 / 3 : ℝ) * Real.log (2 : ℝ) :=
        add_le_add_left hlog_three_le (Real.log (2 : ℝ))
      have halg :
          Real.log (2 : ℝ) + (5 / 3 : ℝ) * Real.log (2 : ℝ) =
            (8 / 3 : ℝ) * Real.log (2 : ℝ) := by
        exact real_one_add_five_thirds_mul_eq_eight_thirds_mul_for_logarithmicPhase
          (Real.log (2 : ℝ))
      exact Eq.subst
        (motive := fun rhs : ℝ => Real.log (2 : ℝ) + Real.log (3 : ℝ) ≤ rhs)
        halg
        hsum
    exact (le_sub_iff_add_le).mpr hmove
  exact Eq.subst
    (motive := fun target : ℝ => Real.log (2 : ℝ) ≤ target)
    hvalue.symm
    htarget

/-- The entropy-form inequality at the lower endpoint `2 log 2`. -/
theorem Complex.real_log_two_le_entropyExpression_at_two_log :
    Real.log (2 : ℝ) ≤
      Complex.realLogDyadicEntropyExpression (2 * Real.log (2 : ℝ)) := by
  have hfour_thirds_lt : (1 : ℝ) < 4 / 3 :=
    real_one_lt_four_div_three_for_logarithmicPhase
  have hfour_thirds_le :
      (4 / 3 : ℝ) ≤ 2 * Real.log (2 : ℝ) := by
    have hlog : (2 / 3 : ℝ) ≤ Real.log (2 : ℝ) :=
      Complex.two_thirds_le_real_log_two
    have hscaled :
        2 * (2 / 3 : ℝ) ≤ 2 * Real.log (2 : ℝ) :=
      mul_le_mul_of_nonneg_left hlog zero_lt_two.le
    have hleft : 2 * (2 / 3 : ℝ) = (4 / 3 : ℝ) := by
      exact Real.two_mul_two_div_three_eq_four_div_three_for_logarithmicPhase
    exact Eq.subst
      (motive := fun left : ℝ => left ≤ 2 * Real.log (2 : ℝ))
      hleft
      hscaled
  have hmono :
      Complex.realLogDyadicEntropyExpression (4 / 3 : ℝ) ≤
        Complex.realLogDyadicEntropyExpression (2 * Real.log (2 : ℝ)) :=
    Complex.realLogDyadicEntropyExpression_monotoneOn_Ici_of_one_lt
      hfour_thirds_lt
      le_rfl
      hfour_thirds_le
      hfour_thirds_le
  exact le_trans
    Complex.real_log_two_le_entropyExpression_at_four_thirds
    hmono

/-- Entropy-form inequality behind the dyadic critical value on the true
interval needed by the critical point: `2 log 2 ≤ y ≤ 2`.

The stronger-looking statement on all of `(1,2]` is false, since the
entropy-form expression is increasing and tends to `0` as `y → 1+`. -/
theorem Complex.real_log_two_le_entropyExpression_on_two_log_two
    {y : ℝ}
    (hy_lower : 2 * Real.log (2 : ℝ) ≤ y) :
    Real.log (2 : ℝ) ≤ y * Real.log y - (y - 1) * Real.log (y - 1) := by
  have hbase :
      Real.log (2 : ℝ) ≤
        Complex.realLogDyadicEntropyExpression (2 * Real.log (2 : ℝ)) :=
    Complex.real_log_two_le_entropyExpression_at_two_log
  have hmono :
      Complex.realLogDyadicEntropyExpression (2 * Real.log (2 : ℝ)) ≤
        Complex.realLogDyadicEntropyExpression y :=
    Complex.realLogDyadicEntropyExpression_monotoneOn_Ici_two_log
      le_rfl
      hy_lower
      hy_lower
  have hdef :
      Complex.realLogDyadicEntropyExpression y =
        y * Real.log y - (y - 1) * Real.log (y - 1) := by
    rfl
  exact Eq.subst
    (motive := fun target : ℝ => Real.log (2 : ℝ) ≤ target)
    hdef
    (le_trans hbase hmono)

/-- The critical expression is the entropy-form expression at
`y = 2 log 2`. -/
theorem Complex.realLogDyadicComparisonCriticalExpression_eq_entropy :
    (2 *
        Real.log
          ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
          Real.log (2 : ℝ) -
        Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) =
      (2 * Real.log (2 : ℝ)) * Real.log (2 * Real.log (2 : ℝ)) -
        ((2 * Real.log (2 : ℝ)) - 1) *
          Real.log ((2 * Real.log (2 : ℝ)) - 1) -
        Real.log (2 : ℝ) := by
  have hL_pos : 0 < Real.log (2 : ℝ) :=
    Complex.real_log_two_pos
  have hY_pos : 0 < 2 * Real.log (2 : ℝ) :=
    mul_pos zero_lt_two hL_pos
  have hD_pos : 0 < 2 * Real.log (2 : ℝ) - 1 :=
    Complex.realLogDyadicComparisonCriticalPoint_den_pos
  have hY_ne : 2 * Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt hY_pos
  have hD_ne : 2 * Real.log (2 : ℝ) - 1 ≠ 0 :=
    ne_of_gt hD_pos
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have hlog_y_div :
      Real.log ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1)) =
        Real.log (2 * Real.log (2 : ℝ)) -
          Real.log (2 * Real.log (2 : ℝ) - 1) :=
    Real.log_div hY_ne hD_ne
  have hlog_two_div :
      Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) =
        Real.log (2 : ℝ) - Real.log (2 * Real.log (2 : ℝ) - 1) :=
    Real.log_div htwo_ne hD_ne
  calc
    (2 *
        Real.log
          ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
          Real.log (2 : ℝ) -
        Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) =
        (2 *
          (Real.log (2 * Real.log (2 : ℝ)) -
            Real.log (2 * Real.log (2 : ℝ) - 1))) *
            Real.log (2 : ℝ) -
          (Real.log (2 : ℝ) - Real.log (2 * Real.log (2 : ℝ) - 1)) := by
      exact congrArg₂ Sub.sub
        (congrArg (fun z : ℝ => (2 * z) * Real.log (2 : ℝ)) hlog_y_div)
        hlog_two_div
    _ =
      (2 * Real.log (2 : ℝ)) * Real.log (2 * Real.log (2 : ℝ)) -
        ((2 * Real.log (2 : ℝ)) - 1) *
          Real.log ((2 * Real.log (2 : ℝ)) - 1) -
        Real.log (2 : ℝ) := by
      exact real_critical_expression_expand_for_logarithmicPhase
        (Real.log (2 * Real.log (2 : ℝ)))
        (Real.log (2 * Real.log (2 : ℝ) - 1))
        (Real.log (2 : ℝ))

/-- Numerical inequality for the dyadic-log defect at its critical point,
written only in terms of `log 2`. -/
theorem Complex.realLogDyadicComparisonCriticalExpression_nonneg :
    0 ≤
      (2 *
        Real.log
          ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
          Real.log (2 : ℝ) -
        Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) := by
  have hY_one : 1 < 2 * Real.log (2 : ℝ) := by
    exact sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos
  have hentropy :
      Real.log (2 : ℝ) ≤
        (2 * Real.log (2 : ℝ)) * Real.log (2 * Real.log (2 : ℝ)) -
          ((2 * Real.log (2 : ℝ)) - 1) *
            Real.log ((2 * Real.log (2 : ℝ)) - 1) :=
    Complex.real_log_two_le_entropyExpression_on_two_log_two le_rfl
  have hnormalized_nonneg :
      0 ≤
        (2 * Real.log (2 : ℝ)) * Real.log (2 * Real.log (2 : ℝ)) -
          ((2 * Real.log (2 : ℝ)) - 1) *
            Real.log ((2 * Real.log (2 : ℝ)) - 1) -
          Real.log (2 : ℝ) :=
    sub_nonneg.mpr hentropy
  exact Eq.subst
    (motive := fun target : ℝ => 0 ≤ target)
    Complex.realLogDyadicComparisonCriticalExpression_eq_entropy.symm
    hnormalized_nonneg

/-- The defect value at the critical point is the explicit numeric critical
expression. -/
theorem Complex.realLogDyadicComparisonDefect_critical_eq_expression :
    Complex.realLogDyadicComparisonDefect
        Complex.realLogDyadicComparisonCriticalPoint =
      (2 *
        Real.log
          ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
          Real.log (2 : ℝ) -
        Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) := by
  have hadd_two :
      Complex.realLogDyadicComparisonCriticalPoint + 2 =
        (2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1) :=
    Complex.realLogDyadicComparisonCriticalPoint_add_two_eq
  have hadd_one :
      Complex.realLogDyadicComparisonCriticalPoint + 1 =
        1 / (2 * Real.log (2 : ℝ) - 1) :=
    Complex.realLogDyadicComparisonCriticalPoint_add_one_eq
  have hmul :
      2 * (Complex.realLogDyadicComparisonCriticalPoint + 1) =
        2 / (2 * Real.log (2 : ℝ) - 1) := by
    calc
      2 * (Complex.realLogDyadicComparisonCriticalPoint + 1) =
          2 * (1 / (2 * Real.log (2 : ℝ) - 1)) := by
        exact congrArg (fun z : ℝ => 2 * z) hadd_one
      _ = 2 / (2 * Real.log (2 : ℝ) - 1) := by
        exact mul_one_div 2 (2 * Real.log (2 : ℝ) - 1)
  calc
    Complex.realLogDyadicComparisonDefect
        Complex.realLogDyadicComparisonCriticalPoint =
        (2 * Real.log (Complex.realLogDyadicComparisonCriticalPoint + 2)) *
          Real.log (2 : ℝ) -
          Real.log (2 * (Complex.realLogDyadicComparisonCriticalPoint + 1)) := by
      rfl
    _ =
        (2 *
          Real.log
            ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
            Real.log (2 : ℝ) -
          Real.log (2 * (Complex.realLogDyadicComparisonCriticalPoint + 1)) := by
      exact congrArg
        (fun z : ℝ => (2 * Real.log z) * Real.log (2 : ℝ) -
          Real.log (2 * (Complex.realLogDyadicComparisonCriticalPoint + 1)))
        hadd_two
    _ =
        (2 *
          Real.log
            ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
            Real.log (2 : ℝ) -
          Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) := by
      exact congrArg
        (fun z : ℝ =>
          (2 *
            Real.log
              ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
              Real.log (2 : ℝ) -
            Real.log z)
        hmul

/-- The critical value of the dyadic-log comparison defect is nonnegative. -/
theorem Complex.realLogDyadicComparisonDefect_critical_nonneg :
    0 ≤
      Complex.realLogDyadicComparisonDefect
        Complex.realLogDyadicComparisonCriticalPoint := by
  exact Eq.subst
    (motive := fun target : ℝ => 0 ≤ target)
    Complex.realLogDyadicComparisonDefect_critical_eq_expression.symm
    Complex.realLogDyadicComparisonCriticalExpression_nonneg

/-- Left branch of the critical-point minimum argument for the dyadic defect. -/
theorem Complex.realLogDyadicComparisonDefect_nonneg_of_le_critical
    {x : ℝ}
    (hx : 0 ≤ x)
    (hx_left : x ≤ Complex.realLogDyadicComparisonCriticalPoint) :
    0 ≤ Complex.realLogDyadicComparisonDefect x := by
  have hanti :
      Complex.realLogDyadicComparisonDefect
          Complex.realLogDyadicComparisonCriticalPoint ≤
        Complex.realLogDyadicComparisonDefect x :=
    Complex.realLogDyadicComparisonDefect_antitoneOn_left
      ⟨hx, hx_left⟩
      ⟨Complex.realLogDyadicComparisonCriticalPoint_nonneg, le_rfl⟩
      hx_left
  exact le_trans Complex.realLogDyadicComparisonDefect_critical_nonneg hanti

/-- Right branch of the critical-point minimum argument for the dyadic defect. -/
theorem Complex.realLogDyadicComparisonDefect_nonneg_of_critical_le
    {x : ℝ}
    (hx_right : Complex.realLogDyadicComparisonCriticalPoint ≤ x) :
    0 ≤ Complex.realLogDyadicComparisonDefect x := by
  have hmono :
      Complex.realLogDyadicComparisonDefect
          Complex.realLogDyadicComparisonCriticalPoint ≤
        Complex.realLogDyadicComparisonDefect x :=
    Complex.realLogDyadicComparisonDefect_monotoneOn_right
      (show Complex.realLogDyadicComparisonCriticalPoint ∈
          Set.Ici Complex.realLogDyadicComparisonCriticalPoint from
        show Complex.realLogDyadicComparisonCriticalPoint ≤
            Complex.realLogDyadicComparisonCriticalPoint from le_rfl)
      hx_right
      hx_right
  exact le_trans Complex.realLogDyadicComparisonDefect_critical_nonneg hmono

/-- One-variable calculus root for the sharp dyadic-log comparison.

The derivative is
`2 log 2 / (x + 2) - 1 / (x + 1)`, so the unique critical point on
`[0,∞)` gives the global minimum; evaluating there is positive. -/
theorem Complex.realLogDyadicComparisonDefect_nonneg
    {x : ℝ}
    (hx : 0 ≤ x)
    [Decidable (x ≤ Complex.realLogDyadicComparisonCriticalPoint)] :
    0 ≤ Complex.realLogDyadicComparisonDefect x := by
  exact
    match (inferInstance : Decidable (x ≤ Complex.realLogDyadicComparisonCriticalPoint)) with
    | isTrue hx_left =>
        Complex.realLogDyadicComparisonDefect_nonneg_of_le_critical hx hx_left
    | isFalse hx_not_left =>
        have hx_right :
            Complex.realLogDyadicComparisonCriticalPoint ≤ x :=
          (lt_of_not_ge hx_not_left).le
        Complex.realLogDyadicComparisonDefect_nonneg_of_critical_le hx_right

/-- The exact real inequality behind the dyadic-log comparison.

Equivalently, `log (2 * (x + 1)) / log 2 ≤ 2 log (x + 2)` for `x ≥ 0`.
This is the monotonic one-variable estimate needed to keep the downstream
constant `2`. -/
theorem Complex.real_log_two_mul_one_add_le_two_log_shift_mul_log_two
    {x : ℝ}
    (hx : 0 ≤ x)
    [Decidable (x ≤ Complex.realLogDyadicComparisonCriticalPoint)] :
    Real.log (2 * (x + 1)) ≤
      (2 * Real.log (x + 2)) * Real.log (2 : ℝ) := by
  have hdefect :
      0 ≤
        (2 * Real.log (x + 2)) * Real.log (2 : ℝ) -
          Real.log (2 * (x + 1)) := by
    exact Complex.realLogDyadicComparisonDefect_nonneg hx
  exact sub_nonneg.mp hdefect

/-- Natural-number specialization of the real logarithmic comparison behind
the dyadic-log estimate. -/
theorem Complex.real_log_two_mul_nat_succ_le_two_log_shift_mul_log_two
    (N : ℕ)
    [Decidable ((N : ℝ) ≤ Complex.realLogDyadicComparisonCriticalPoint)] :
    Real.log ((((N + 1) * 2 : ℕ) : ℝ)) ≤
      (2 * Real.log (2 + N)) * Real.log (2 : ℝ) := by
  have hreal :
      Real.log (2 * (((N : ℝ) + 1))) ≤
        (2 * Real.log ((N : ℝ) + 2)) * Real.log (2 : ℝ) :=
    Complex.real_log_two_mul_one_add_le_two_log_shift_mul_log_two
      (Nat.cast_nonneg N)
  have harg :
      ((((N + 1) * 2 : ℕ) : ℝ)) = 2 * (((N : ℝ) + 1)) := by
    exact real_nat_succ_mul_two_cast_eq_for_logarithmicPhase N
  have hshift :
      ((N : ℝ) + 2) = 2 + N := by
    exact real_nat_add_two_comm_for_logarithmicPhase N
  exact Eq.subst
    (motive := fun arg : ℝ =>
      Real.log arg ≤ (2 * Real.log (2 + N)) * Real.log (2 : ℝ))
    harg.symm
    (Eq.subst
      (motive := fun shift : ℝ =>
        Real.log (2 * ((N : ℝ) + 1)) ≤
          (2 * Real.log shift) * Real.log (2 : ℝ))
      hshift
      hreal)

/-- Real-logarithm comparison for the doubled shifted natural cutoff. -/
theorem Complex.real_logb_two_mul_nat_succ_le_two_log_shift
    (N : ℕ)
    [Decidable ((N : ℝ) ≤ Complex.realLogDyadicComparisonCriticalPoint)] :
    Real.logb (2 : ℝ) (((N + 1) * 2 : ℕ) : ℝ) ≤
      2 * Real.log (2 + N) := by
  have hlog2_pos : 0 < Real.log (2 : ℝ) :=
    Complex.real_log_two_pos
  have hraw :
      Real.log ((((N + 1) * 2 : ℕ) : ℝ)) ≤
        (2 * Real.log (2 + N)) * Real.log (2 : ℝ) :=
    Complex.real_log_two_mul_nat_succ_le_two_log_shift_mul_log_two N
  have hdiv :
      Real.log ((((N + 1) * 2 : ℕ) : ℝ)) / Real.log (2 : ℝ) ≤
        2 * Real.log (2 + N) := by
    exact (div_le_iff₀ hlog2_pos).mpr hraw
  have hlogb :
      Real.logb (2 : ℝ) (((N + 1) * 2 : ℕ) : ℝ) =
        Real.log ((((N + 1) * 2 : ℕ) : ℝ)) / Real.log (2 : ℝ) := by
    rfl
  exact Eq.subst
    (motive := fun lhs : ℝ => lhs ≤ 2 * Real.log (2 + N))
    hlogb.symm
    hdiv


/-- Dyadic integer logarithm is dominated by twice the natural logarithm on the
shifted natural cutoff. -/
theorem Complex.nat_log2_add_one_le_two_log
    (N : ℕ)
    [Decidable ((N : ℝ) ≤ Complex.realLogDyadicComparisonCriticalPoint)] :
    (Nat.log2 (N + 1) : ℝ) + 1 ≤ 2 * Real.log (2 + N) := by
  have hnat_eq :
      Nat.log2 (N + 1) + 1 = Nat.log 2 ((N + 1) * 2) :=
    Complex.nat_log2_add_one_eq_nat_log_two_mul_succ N
  have hcast_eq :
      ((Nat.log2 (N + 1) : ℝ) + 1) =
        (Nat.log 2 ((N + 1) * 2) : ℝ) := by
    exact Eq.trans
      (Eq.trans
        (congrArg (fun r : ℝ => (Nat.log2 (N + 1) : ℝ) + r) Nat.cast_one.symm)
        (Nat.cast_add (Nat.log2 (N + 1)) 1).symm)
      (congrArg (fun n : ℕ => (n : ℝ)) hnat_eq)
  have hbridge :
      (Nat.log 2 ((N + 1) * 2) : ℝ) ≤
        Real.logb (2 : ℝ) (((N + 1) * 2 : ℕ) : ℝ) :=
    Real.natLog_le_logb ((N + 1) * 2) 2
  have hreal :
      Real.logb (2 : ℝ) (((N + 1) * 2 : ℕ) : ℝ) ≤
        2 * Real.log (2 + N) :=
    Complex.real_logb_two_mul_nat_succ_le_two_log_shift N
  exact Eq.subst
    (motive := fun lhs : ℝ => lhs ≤ 2 * Real.log (2 + N))
    hcast_eq.symm
    (le_trans hbridge hreal)

/-- The transition square-root factor is at least `2` at nonzero boundary
frequency. -/
theorem Complex.two_le_two_mul_sqrt_one_add_norm
    (t : ℝ) :
    2 ≤ 2 * Real.sqrt (1 + ‖t‖) := by
  have hone_le : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_arg : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact (Real.one_le_sqrt).mpr hone_arg
  exact
    Eq.subst
      (motive := fun lhs : ℝ => lhs ≤ 2 * Real.sqrt (1 + ‖t‖))
      (mul_one 2)
      (mul_le_mul_of_nonneg_left hone_le zero_le_two)

/-- The dyadic counting term is absorbed by the standard
`sqrt(1 + |t|) log(2+N)` transition factor. -/
theorem Complex.logarithmicPhase_log2_add_one_le_sqrt_transition
    (t : ℝ)
    (N : ℕ)
    [Decidable ((N : ℝ) ≤ Complex.realLogDyadicComparisonCriticalPoint)] :
    (Nat.log2 (N + 1) : ℝ) + 1 ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) := by
  have hlog2 :
      (Nat.log2 (N + 1) : ℝ) + 1 ≤ 2 * Real.log (2 + N) :=
    Complex.nat_log2_add_one_le_two_log N
  have htarget :
      2 * Real.log (2 + N) ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) := by
    have hlog_nonneg : 0 ≤ Real.log (2 + N) :=
      le_trans real_zero_le_one_div_two_for_logarithmicPhase
        (Complex.logarithmicPhase_standardLog_half_le N)
    have hsqrt_factor : 2 ≤ 2 * Real.sqrt (1 + ‖t‖) :=
      Complex.two_le_two_mul_sqrt_one_add_norm t
    exact mul_le_mul_of_nonneg_right hsqrt_factor hlog_nonneg
  exact le_trans hlog2 htarget

/-- The quotient term in the dyadic-cover expression is absorbed by the
standard logarithmic factor. -/
theorem Complex.logarithmicPhase_quotient_term_le_standard
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ) :
    8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) ≤
      16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) := by
  have hlog_half : (1 / 2 : ℝ) ≤ Real.log (2 + N) :=
    Complex.logarithmicPhase_standardLog_half_le N
  have hquot_nonneg : 0 ≤ (((N + 1 : ℕ) : ℝ) / ‖t‖) := by
    have ht_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    exact div_nonneg (Nat.cast_nonneg (N + 1)) ht_pos.le
  have hscaled :
      16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * (1 / 2 : ℝ) ≤
        16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) := by
    have hfactor_nonneg : 0 ≤ 16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) :=
      mul_nonneg (Nat.cast_nonneg 16) hquot_nonneg
    exact mul_le_mul_of_nonneg_left hlog_half hfactor_nonneg
  have hleft :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) =
        16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * (1 / 2 : ℝ) := by
    exact real_eight_mul_eq_sixteen_mul_half_for_logarithmicPhase
      (((N + 1 : ℕ) : ℝ) / ‖t‖)
  exact Eq.subst
    (motive := fun lhs : ℝ =>
      lhs ≤ 16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N))
    hleft.symm
    hscaled

/-- The dyadic counting term in the cover expression is absorbed by the
standard transition factor. -/
theorem Complex.logarithmicPhase_counting_term_le_standard
    (t : ℝ)
    (N : ℕ)
    [Decidable ((N : ℝ) ≤ Complex.realLogDyadicComparisonCriticalPoint)] :
    8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤
      16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) := by
  have htransition :
      (Nat.log2 (N + 1) : ℝ) + 1 ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) :=
    Complex.logarithmicPhase_log2_add_one_le_sqrt_transition t N
  have hleft_nonneg : (0 : ℝ) ≤ 8 :=
    Nat.cast_nonneg 8
  have hscaled :
      8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤
        8 * (2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N)) :=
    mul_le_mul_of_nonneg_left htransition hleft_nonneg
  have hright :
      8 * (2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N)) =
        16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) := by
    exact real_eight_two_mul_log_scale_for_logarithmicPhase
      (Real.sqrt (1 + ‖t‖))
      (Real.log (2 + N))
  exact Eq.subst
    (motive := fun rhs : ℝ =>
      8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤ rhs)
    hright
    hscaled

/-- Elementary comparison from the dyadic block-cover expression to the
standard logarithmic first-derivative bound. -/
theorem Complex.logarithmicPhase_dyadic_cover_expression_le_standard
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ)
    [Decidable ((N : ℝ) ≤ Complex.realLogDyadicComparisonCriticalPoint)] :
    8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) ≤
      16 *
        (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + N) := by
  have hquot :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) ≤
        16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) :=
    Complex.logarithmicPhase_quotient_term_le_standard t ht N
  have hcount :
      8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤
        16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) :=
    Complex.logarithmicPhase_counting_term_le_standard t N
  have hsum :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) +
          8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤
        16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) +
          16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) :=
    add_le_add hquot hcount
  have hleft :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) =
        8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) +
          8 * ((Nat.log2 (N + 1) : ℝ) + 1) := by
    exact real_eight_mul_three_term_split_for_logarithmicPhase
      (((N + 1 : ℕ) : ℝ) / ‖t‖)
      (Nat.log2 (N + 1) : ℝ)
  have hright :
      16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) +
          16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) =
        16 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N) := by
    exact real_sixteen_mul_sum_log_factor_for_logarithmicPhase
      (((N + 1 : ℕ) : ℝ) / ‖t‖)
      (Real.sqrt (1 + ‖t‖))
      (Real.log (2 + N))
  exact Eq.subst
    (motive := fun lhs : ℝ =>
      lhs ≤
        16 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N))
    hleft.symm
    (Eq.subst
      (motive := fun rhs : ℝ =>
        8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) +
            8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤ rhs)
      hright
      hsum)
end

end LFunctions
end Boundary
