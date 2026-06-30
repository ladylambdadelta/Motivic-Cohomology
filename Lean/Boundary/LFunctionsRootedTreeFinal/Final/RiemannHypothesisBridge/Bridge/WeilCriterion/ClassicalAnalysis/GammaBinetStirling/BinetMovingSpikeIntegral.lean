import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetMovingLogWeighted
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Real moving-spike integral estimates for the Binet branch wall

This file owns the real-variable estimates used to integrate the moving
branch-wall spike in the far upper-center Binet branch.  The Binet files should
consume these lemmas rather than carrying the interval-integral arithmetic
inline.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- The real half is positive. -/
theorem Real.zero_lt_one_half :
    (0 : ℝ) < (1 / 2 : ℝ) := by
  exact one_half_pos

/-- The exponent `-1/2` is locally integrable at the origin. -/
theorem Real.neg_one_lt_neg_half :
    (-1 : ℝ) < -(1 / 2 : ℝ) := by
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
  exact neg_lt_neg hhalf_lt_one

/-- The antiderivative exponent for `x ^ (-1/2)` is `1/2`. -/
theorem Real.neg_half_add_one_eq_half :
    -(1 / 2 : ℝ) + 1 = (1 / 2 : ℝ) := by
  calc
    -(1 / 2 : ℝ) + 1 = 1 - (1 / 2 : ℝ) := by
      exact add_comm (-(1 / 2 : ℝ)) 1
    _ = (1 / 2 : ℝ) := by
      exact sub_half 1

/-- The denominator in the `x ^ (-1/2)` antiderivative is positive. -/
theorem Real.neg_half_add_one_pos :
    0 < -(1 / 2 : ℝ) + 1 := by
  exact Eq.subst
    (motive := fun x : ℝ => 0 < x)
    Real.neg_half_add_one_eq_half.symm
    Real.zero_lt_one_half

/-- The inverse of `1/2` is `2`. -/
theorem Real.inv_one_half_eq_two :
    ((1 : ℝ) / 2)⁻¹ = 2 := by
  have hhalf_eq : ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ := by
    exact one_div 2
  calc
    ((1 : ℝ) / 2)⁻¹ = ((2 : ℝ)⁻¹)⁻¹ := by
      exact congrArg Inv.inv hhalf_eq
    _ = (2 : ℝ) := by
      exact inv_inv (2 : ℝ)

/-- The basic positive-side antiderivative value for the square-root spike. -/
theorem Real.integral_zero_to_rpow_neg_half
    {R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    (∫ x in (0)..R, x ^ (-(1 / 2 : ℝ)) : ℝ)
      =
    R ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) := by
  have hIntegral :
      (∫ x in (0)..R, x ^ (-(1 / 2 : ℝ)) : ℝ)
        =
      (R ^ (-(1 / 2 : ℝ) + 1) - (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1)) /
        (-(1 / 2 : ℝ) + 1) :=
    integral_rpow (a := (0 : ℝ)) (b := R)
      (r := -(1 / 2 : ℝ))
      (Or.inl Real.neg_one_lt_neg_half)
  have hZero :
      (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 0 := by
    exact Real.zero_rpow
      (ne_of_gt Real.neg_half_add_one_pos)
  have hTop :
      R ^ (-(1 / 2 : ℝ) + 1) =
        R ^ ((1 : ℝ) / 2) := by
    exact congrArg (fun x : ℝ => R ^ x)
      Real.neg_half_add_one_eq_half
  have hDen :
      (-(1 / 2 : ℝ) + 1) = ((1 : ℝ) / 2) :=
    Real.neg_half_add_one_eq_half
  calc
    (∫ x in (0)..R, x ^ (-(1 / 2 : ℝ)) : ℝ)
        =
        (R ^ (-(1 / 2 : ℝ) + 1) - (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1)) /
          (-(1 / 2 : ℝ) + 1) := by
          exact hIntegral
    _ =
        (R ^ ((1 : ℝ) / 2) - 0) / ((1 : ℝ) / 2) := by
          exact congrArg₂
            (fun x y : ℝ => x / y)
            (congrArg₂
              (fun x y : ℝ => x - y)
              hTop
              hZero)
            hDen
    _ =
        R ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) := by
          exact congrArg
            (fun x : ℝ => x / ((1 : ℝ) / 2))
            (sub_zero (R ^ ((1 : ℝ) / 2)))

/-- The positive-side square-root spike integral is twice the square-root
scale. -/
theorem Real.integral_zero_to_rpow_neg_half_eq_two_mul
    {R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    (∫ x in (0)..R, x ^ (-(1 / 2 : ℝ)) : ℝ)
      =
    2 * R ^ ((1 : ℝ) / 2) := by
  have hIntegral :
      (∫ x in (0)..R, x ^ (-(1 / 2 : ℝ)) : ℝ)
        =
      R ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) :=
    Real.integral_zero_to_rpow_neg_half hR_nonneg
  have hDiv :
      R ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2)
        =
      2 * R ^ ((1 : ℝ) / 2) := by
    calc
      R ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2)
          =
          R ^ ((1 : ℝ) / 2) * (((1 : ℝ) / 2)⁻¹) := by
            exact div_eq_mul_inv
              (R ^ ((1 : ℝ) / 2))
              ((1 : ℝ) / 2)
      _ =
          R ^ ((1 : ℝ) / 2) * 2 := by
            exact congrArg
              (fun x : ℝ => R ^ ((1 : ℝ) / 2) * x)
              Real.inv_one_half_eq_two
      _ =
          2 * R ^ ((1 : ℝ) / 2) := by
            exact mul_comm (R ^ ((1 : ℝ) / 2)) 2
  exact Eq.trans hIntegral hDiv

/-- The half exponent is at most the unit exponent. -/
theorem Real.one_half_le_one :
    ((1 : ℝ) / 2) ≤ 1 := by
  have htwo_pos : 0 < (2 : ℝ) :=
    zero_lt_two
  exact (div_le_iff₀ htwo_pos).mpr
    (show (1 : ℝ) ≤ 1 * 2 by
      exact
        Eq.subst
          (motive := fun x : ℝ => (1 : ℝ) ≤ x)
          (one_mul (2 : ℝ)).symm
          one_le_two)

/-- For height at least one, the square-root scale is bounded by the height. -/
theorem Real.rpow_half_le_self_of_one_le
    {N : ℝ}
    (hN_one : 1 ≤ N) :
    N ^ ((1 : ℝ) / 2) ≤ N := by
  have hpow :
      N ^ ((1 : ℝ) / 2) ≤ N ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN_one Real.one_half_le_one
  have hone :
      N ^ (1 : ℝ) = N :=
    Real.rpow_one N
  exact
    Eq.subst
      (motive := fun x : ℝ => N ^ ((1 : ℝ) / 2) ≤ x)
      hone
      hpow

/-- Heights at least two dominate their square-root scale. -/
theorem Real.rpow_half_le_self_of_two_le
    {N : ℝ}
    (hN_two : 2 ≤ N) :
    N ^ ((1 : ℝ) / 2) ≤ N := by
  have hN_one : 1 ≤ N :=
    le_trans one_le_two hN_two
  exact Real.rpow_half_le_self_of_one_le hN_one

/-- On the positive half-line, `|x|^(-1/2)` is the usual real power. -/
theorem Real.abs_rpow_neg_half_eq_rpow_of_nonneg
    {x : ℝ}
    (hx_nonneg : 0 ≤ x) :
    |x| ^ (-(1 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) := by
  exact congrArg
    (fun y : ℝ => y ^ (-(1 / 2 : ℝ)))
    (abs_of_nonneg hx_nonneg)

/-- On the negative half-line, `|x|^(-1/2)` reflects to `(-x)^(-1/2)`. -/
theorem Real.abs_rpow_neg_half_eq_neg_rpow_of_nonpos
    {x : ℝ}
    (hx_nonpos : x ≤ 0) :
    |x| ^ (-(1 / 2 : ℝ)) = (-x) ^ (-(1 / 2 : ℝ)) := by
  exact congrArg
    (fun y : ℝ => y ^ (-(1 / 2 : ℝ)))
    (abs_of_nonpos hx_nonpos)

/-- The positive interval integral of `|x|^(-1/2)` is twice the square-root
scale. -/
theorem Real.integral_zero_to_abs_rpow_neg_half_eq_two_mul
    {R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    (∫ x in (0)..R, |x| ^ (-(1 / 2 : ℝ)) : ℝ)
      =
    2 * R ^ ((1 : ℝ) / 2) := by
  have hEqOn :
      Set.EqOn
        (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
        (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
        (Set.uIcc (0 : ℝ) R) := by
    intro x hx
    have huIcc :
        Set.uIcc (0 : ℝ) R = Set.Icc (0 : ℝ) R :=
      Set.uIcc_of_le hR_nonneg
    have hxIcc : x ∈ Set.Icc (0 : ℝ) R :=
      Eq.subst
        (motive := fun S : Set ℝ => x ∈ S)
        huIcc
        hx
    have hx_nonneg : 0 ≤ x :=
      hxIcc.1
    exact Real.abs_rpow_neg_half_eq_rpow_of_nonneg hx_nonneg
  have hintegral_eq :
      (∫ x in (0)..R, |x| ^ (-(1 / 2 : ℝ)) : ℝ)
        =
      ∫ x in (0)..R, x ^ (-(1 / 2 : ℝ)) :=
    intervalIntegral.integral_congr hEqOn
  exact Eq.trans hintegral_eq
    (Real.integral_zero_to_rpow_neg_half_eq_two_mul hR_nonneg)

/-- The negative half of the symmetric square-root spike integral equals the
positive half by reflection. -/
theorem Real.integral_neg_to_zero_abs_rpow_neg_half_eq_two_mul
    {R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    (∫ x in (-R)..0, |x| ^ (-(1 / 2 : ℝ)) : ℝ)
      =
    2 * R ^ ((1 : ℝ) / 2) := by
  have hreflect :
      (∫ x in (-R)..0, |x| ^ (-(1 / 2 : ℝ)) : ℝ)
        =
      ∫ x in (0 : ℝ)..R, |x| ^ (-(1 / 2 : ℝ)) := by
    have hcomp :
        (∫ x in (-R)..0, |(-x)| ^ (-(1 / 2 : ℝ)) : ℝ)
          =
      ∫ x in (-(0 : ℝ))..-(-R), |x| ^ (-(1 / 2 : ℝ)) :=
      intervalIntegral.integral_comp_neg
        (f := fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
    have hleft :
        (∫ x in (-R)..0, |x| ^ (-(1 / 2 : ℝ)) : ℝ)
          =
        ∫ x in (-R)..0, |(-x)| ^ (-(1 / 2 : ℝ)) := by
      exact intervalIntegral.integral_congr
        (fun x _hx =>
          congrArg
            (fun y : ℝ => y ^ (-(1 / 2 : ℝ)))
            (abs_neg x).symm)
    have hright :
        (∫ x in (-(0 : ℝ))..-(-R), |x| ^ (-(1 / 2 : ℝ)) : ℝ)
          =
        ∫ x in (0 : ℝ)..R, |x| ^ (-(1 / 2 : ℝ)) := by
      have hzero : (-(0 : ℝ)) = 0 :=
        neg_zero
      have hnegneg : -(-R) = R :=
        neg_neg R
      exact congrArg₂
        (fun a b : ℝ =>
          ∫ x in a..b, |x| ^ (-(1 / 2 : ℝ)))
        hzero hnegneg
    exact Eq.trans hleft (Eq.trans hcomp hright)
  exact Eq.trans hreflect
    (Real.integral_zero_to_abs_rpow_neg_half_eq_two_mul hR_nonneg)

/-- The positive half of the symmetric square-root spike is interval-integrable. -/
theorem Real.intervalIntegrable_zero_to_pos_abs_rpow_neg_half
    {R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    IntervalIntegrable
      (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
      volume 0 R := by
  have hrpowInt :
      IntervalIntegrable
        (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
        volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' Real.neg_one_lt_neg_half
  exact hrpowInt.congr
    ((ae_restrict_iff' measurableSet_uIoc).mpr
      (Eventually.of_forall
        (fun x hx =>
          have huIcc :
              Set.uIcc (0 : ℝ) R = Set.Icc (0 : ℝ) R :=
            Set.uIcc_of_le hR_nonneg
          have hxuIcc : x ∈ Set.uIcc (0 : ℝ) R :=
            Set.uIoc_subset_uIcc hx
          have hxIcc : x ∈ Set.Icc (0 : ℝ) R :=
            Eq.subst
              (motive := fun S : Set ℝ => x ∈ S)
              huIcc
              hxuIcc
          have hx_nonneg : 0 ≤ x :=
            hxIcc.1
          (Real.abs_rpow_neg_half_eq_rpow_of_nonneg hx_nonneg).symm)))

/-- The negative half of the symmetric square-root spike is interval-integrable. -/
theorem Real.intervalIntegrable_neg_to_zero_abs_rpow_neg_half
    {R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    IntervalIntegrable
      (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
      volume (-R) 0 := by
  have hrightAbsInt :
      IntervalIntegrable
        (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
        volume 0 R :=
    Real.intervalIntegrable_zero_to_pos_abs_rpow_neg_half hR_nonneg
  have hreflect :
      IntervalIntegrable
      (fun x : ℝ => |(-x)| ^ (-(1 / 2 : ℝ)))
      volume (-R) 0 := by
    have hraw :
        IntervalIntegrable
          (fun x : ℝ => |(-x)| ^ (-(1 / 2 : ℝ)))
          volume (-(0 : ℝ)) (-R) :=
      (IntervalIntegrable.iff_comp_neg
        (f := fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
        (a := (0 : ℝ))
        (b := R)).mp hrightAbsInt
    have hsymm :
        IntervalIntegrable
          (fun x : ℝ => |(-x)| ^ (-(1 / 2 : ℝ)))
          volume (-R) (-(0 : ℝ)) :=
      hraw.symm
    have hzero : (-(0 : ℝ)) = 0 :=
      neg_zero
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          IntervalIntegrable
            (fun y : ℝ => |(-y)| ^ (-(1 / 2 : ℝ)))
            volume (-R) x)
        hzero
        hsymm
  exact hreflect.congr
    ((ae_restrict_iff' measurableSet_uIoc).mpr
      (Eventually.of_forall
        (fun x _hx =>
          congrArg
            (fun y : ℝ => y ^ (-(1 / 2 : ℝ)))
            (abs_neg x))))

/-- The symmetric `|x|^(-1/2)` spike integral on `[-R,R]` has the expected
square-root scale. -/
theorem Real.integral_neg_to_pos_abs_rpow_neg_half_eq_four_mul
    {R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    (∫ x in (-R)..R, |x| ^ (-(1 / 2 : ℝ)) : ℝ)
      =
    4 * R ^ ((1 : ℝ) / 2) := by
  have hleftInt :
      IntervalIntegrable
      (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
      volume (-R) 0 :=
    Real.intervalIntegrable_neg_to_zero_abs_rpow_neg_half hR_nonneg
  have hrightInt :
      IntervalIntegrable
      (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
      volume 0 R :=
    Real.intervalIntegrable_zero_to_pos_abs_rpow_neg_half hR_nonneg
  have hadd :
      (∫ x in (-R)..0, |x| ^ (-(1 / 2 : ℝ)) : ℝ) +
          ∫ x in (0 : ℝ)..R, |x| ^ (-(1 / 2 : ℝ)) =
        ∫ x in (-R)..R, |x| ^ (-(1 / 2 : ℝ)) :=
    intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt
  have hleft :
      (∫ x in (-R)..0, |x| ^ (-(1 / 2 : ℝ)) : ℝ)
        =
      2 * R ^ ((1 : ℝ) / 2) :=
    Real.integral_neg_to_zero_abs_rpow_neg_half_eq_two_mul hR_nonneg
  have hright :
      (∫ x in (0 : ℝ)..R, |x| ^ (-(1 / 2 : ℝ)) : ℝ)
        =
      2 * R ^ ((1 : ℝ) / 2) :=
    Real.integral_zero_to_abs_rpow_neg_half_eq_two_mul hR_nonneg
  have hsum :
      (∫ x in (-R)..0, |x| ^ (-(1 / 2 : ℝ)) : ℝ) +
          ∫ x in (0 : ℝ)..R, |x| ^ (-(1 / 2 : ℝ)) =
        4 * R ^ ((1 : ℝ) / 2) := by
    calc
      (∫ x in (-R)..0, |x| ^ (-(1 / 2 : ℝ)) : ℝ) +
          ∫ x in (0 : ℝ)..R, |x| ^ (-(1 / 2 : ℝ)) =
        (2 * R ^ ((1 : ℝ) / 2)) +
          (2 * R ^ ((1 : ℝ) / 2)) := by
        exact congrArg₂ HAdd.hAdd hleft hright
      _ = 4 * R ^ ((1 : ℝ) / 2) := by
        calc
          (2 * R ^ ((1 : ℝ) / 2)) +
              (2 * R ^ ((1 : ℝ) / 2)) =
            (2 + 2) * R ^ ((1 : ℝ) / 2) := by
            exact (add_mul (2 : ℝ) 2 (R ^ ((1 : ℝ) / 2))).symm
          _ = 4 * R ^ ((1 : ℝ) / 2) := by
            exact congrArg
              (fun x : ℝ => x * R ^ ((1 : ℝ) / 2))
              (show (2 : ℝ) + 2 = 4 by
                exact two_add_two_eq_four)
  exact Eq.trans hadd.symm hsum

/-- The symmetric `|x|^(-1/2)` spike is interval-integrable on `[-R,R]`. -/
theorem Real.intervalIntegrable_neg_to_pos_abs_rpow_neg_half
    {R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    IntervalIntegrable
      (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
      volume (-R) R := by
  have hleftInt :
      IntervalIntegrable
        (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
        volume (-R) 0 :=
    Real.intervalIntegrable_neg_to_zero_abs_rpow_neg_half hR_nonneg
  have hrightInt :
      IntervalIntegrable
        (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))
        volume 0 R :=
    Real.intervalIntegrable_zero_to_pos_abs_rpow_neg_half hR_nonneg
  exact hleftInt.trans hrightInt

/-- Translating the symmetric square-root spike interval does not change its
integral. -/
theorem Real.integral_centered_abs_sub_rpow_neg_half_eq_four_mul
    {y R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    (∫ x in (y - R)..(y + R), |y - x| ^ (-(1 / 2 : ℝ)) : ℝ)
      =
    4 * R ^ ((1 : ℝ) / 2) := by
  let F : ℝ → ℝ := fun u : ℝ => |u| ^ (-(1 / 2 : ℝ))
  have hchange :
      (∫ x in (y - R)..(y + R), F (y - x))
        =
      ∫ u in y - (y + R)..y - (y - R), F u :=
    intervalIntegral.integral_comp_sub_left F y
  have hleft :
      y - (y + R) = -R := by
    calc
      y - (y + R) = y + -(y + R) := by
        exact sub_eq_add_neg y (y + R)
      _ = y + (-y + -R) := by
        exact congrArg (fun z : ℝ => y + z) (neg_add y R)
      _ = (y + -y) + -R := by
        exact (add_assoc y (-y) (-R)).symm
      _ = 0 + -R := by
        exact congrArg (fun z : ℝ => z + -R) (add_neg_cancel y)
      _ = -R := by
        exact zero_add (-R)
  have hright :
      y - (y - R) = R := by
    calc
      y - (y - R) = y + -(y - R) := by
        exact sub_eq_add_neg y (y - R)
      _ = y + (-y + R) := by
        have hneg0 : -(y - R) = -y - -R :=
          neg_sub' y R
        have hneg1 : -y - -R = -y + R := by
          exact congrArg (fun z : ℝ => -y + z) (neg_neg R)
        exact congrArg (fun z : ℝ => y + z) (Eq.trans hneg0 hneg1)
      _ = (y + -y) + R := by
        exact (add_assoc y (-y) R).symm
      _ = 0 + R := by
        exact congrArg (fun z : ℝ => z + R) (add_neg_cancel y)
      _ = R := by
        exact zero_add R
  have hnormalized :
      (∫ u in y - (y + R)..y - (y - R), F u)
        =
      ∫ u in (-R)..R, F u := by
    exact congrArg₂
      (fun a b : ℝ => ∫ u in a..b, F u)
      hleft hright
  have hsymmetric :
      (∫ u in (-R)..R, F u)
        =
      4 * R ^ ((1 : ℝ) / 2) :=
    Real.integral_neg_to_pos_abs_rpow_neg_half_eq_four_mul hR_nonneg
  exact Eq.trans hchange (Eq.trans hnormalized hsymmetric)

/-- The translated centered square-root spike is interval-integrable on its
own centered interval. -/
theorem Real.intervalIntegrable_centered_abs_sub_rpow_neg_half
    {y R : ℝ}
    (hR_nonneg : 0 ≤ R) :
    IntervalIntegrable
      (fun x : ℝ => |y - x| ^ (-(1 / 2 : ℝ)))
      volume (y - R) (y + R) := by
  let F : ℝ → ℝ := fun u : ℝ => |u| ^ (-(1 / 2 : ℝ))
  have hbase :
      IntervalIntegrable F volume (-R) R :=
    Real.intervalIntegrable_neg_to_pos_abs_rpow_neg_half hR_nonneg
  have htranslated :
      IntervalIntegrable (fun x : ℝ => F (y - x))
        volume (y - (-R)) (y - R) :=
    hbase.comp_sub_left y
  have hleft :
      y - (-R) = y + R := by
    exact sub_neg_eq_add y R
  have hrev :
      IntervalIntegrable (fun x : ℝ => F (y - x))
        volume (y - R) (y - (-R)) :=
    htranslated.symm
  exact
    Eq.subst
      (motive := fun b : ℝ =>
        IntervalIntegrable (fun x : ℝ => F (y - x))
          volume (y - R) b)
      hleft
      hrev

/-- A single real point is avoided almost everywhere for Lebesgue measure. -/
theorem Real.ae_ne_singleton
    (y : ℝ) :
    ∀ᵐ x : ℝ ∂volume, x ≠ y := by
  have hbad :
      {x : ℝ | ¬ x ≠ y} = {y} := by
    exact Set.ext
      (fun x =>
        Iff.intro
          (fun hx => Set.mem_singleton_iff.mpr (not_not.mp hx))
          (fun hx =>
            have hxy : x = y :=
              Set.mem_singleton_iff.mp hx
            not_not.mpr hxy))
  have hzero :
      volume {x : ℝ | ¬ x ≠ y} = 0 :=
    Eq.subst
      (motive := fun S : Set ℝ => volume S = 0)
      hbad.symm
      (measure_singleton y)
  exact ae_iff.mpr hzero

end

end LFunctions
end Boundary
