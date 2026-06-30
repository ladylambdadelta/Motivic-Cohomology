import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetMovingSpikeIntegral

/-!
# Arithmetic support for far upper-center moving logarithmic estimates

This file owns the small numeral and norm inequalities used by the far
upper-center branch estimates.  Keeping these facts named prevents the analytic
owner file from carrying local arithmetic proof search.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

theorem Real.zero_lt_eight :
    (0 : ℝ) < 8 := by
  have hsum : (4 : ℝ) + 4 = 8 := by
    have hnat : (4 : ℕ) + 4 = 8 := by
      rfl
    calc
      (4 : ℝ) + 4 = (((4 : ℕ) + 4 : ℕ) : ℝ) := by
        exact (Nat.cast_add 4 4).symm
      _ = 8 := by
        exact congrArg (fun n : ℕ => (n : ℝ)) hnat
  have hpos : (0 : ℝ) < 4 + 4 :=
    add_pos zero_lt_four zero_lt_four
  exact Eq.subst
    (motive := fun x : ℝ => 0 < x)
    hsum
    hpos

theorem Real.zero_le_eight :
    (0 : ℝ) ≤ 8 :=
  le_of_lt Real.zero_lt_eight

theorem Real.two_mul_three_eq_six :
    (2 : ℝ) * 3 = 6 := by
  have hnat : (2 : ℕ) * 3 = 6 := by
    rfl
  calc
    (2 : ℝ) * 3 = (((2 : ℕ) * 3 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 2 3).symm
    _ = 6 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.eight_eq_two_mul_four :
    (8 : ℝ) = 2 * 4 :=
  Real.two_mul_four_eq_eight.symm

theorem Real.six_sub_one_eq_five :
    (6 : ℝ) - 1 = 5 := by
  have hadd : (5 : ℝ) + 1 = 6 := by
    have hnat : (5 : ℕ) + 1 = 6 := by
      rfl
    calc
      (5 : ℝ) + 1 = (((5 : ℕ) + 1 : ℕ) : ℝ) := by
        have hleft :
            (5 : ℝ) + 1 =
              ((5 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) :=
          congrArg₂ HAdd.hAdd
            (show (5 : ℝ) = ((5 : ℕ) : ℝ) by rfl)
            (Nat.cast_one.symm)
        have hcast :
            ((5 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) =
              (((5 : ℕ) + 1 : ℕ) : ℝ) :=
          (Nat.cast_add 5 1).symm
        exact Eq.trans hleft hcast
      _ = 6 := by
        exact congrArg (fun n : ℕ => (n : ℝ)) hnat
  exact (sub_eq_iff_eq_add).mpr hadd.symm

theorem Real.two_mul_five_eq_ten :
    (2 : ℝ) * 5 = 10 := by
  have hnat : (2 : ℕ) * 5 = 10 := by
    rfl
  calc
    (2 : ℝ) * 5 = (((2 : ℕ) * 5 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 2 5).symm
    _ = 10 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.ten_eq_two_mul_five :
    (10 : ℝ) = 2 * 5 :=
  Real.two_mul_five_eq_ten.symm

theorem Real.three_mul_eight_eq_twenty_four :
    (3 : ℝ) * 8 = 24 := by
  have hnat : (3 : ℕ) * 8 = 24 := by
    rfl
  calc
    (3 : ℝ) * 8 = (((3 : ℕ) * 8 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 3 8).symm
    _ = 24 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.two_le_four_far_upper :
    (2 : ℝ) ≤ 4 := by
  have htwo_add_two : (2 : ℝ) + 2 = 4 :=
    two_add_two_eq_four
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    le_trans zero_le_one one_le_two
  have hle_sum : (2 : ℝ) ≤ 2 + 2 :=
    le_add_of_nonneg_right htwo_nonneg
  exact
    Eq.subst
      (motive := fun x : ℝ => (2 : ℝ) ≤ x)
      htwo_add_two
      hle_sum

theorem Real.four_le_eight_far_upper :
    (4 : ℝ) ≤ 8 := by
  have hfour_add_four : (4 : ℝ) + 4 = 8 := by
    have hnat : (4 : ℕ) + 4 = 8 := by
      rfl
    calc
      (4 : ℝ) + 4 = (((4 : ℕ) + 4 : ℕ) : ℝ) := by
        exact (Nat.cast_add 4 4).symm
      _ = 8 := by
        exact congrArg (fun n : ℕ => (n : ℝ)) hnat
  have hfour_nonneg : (0 : ℝ) ≤ 4 :=
    zero_le_four
  have hle_sum : (4 : ℝ) ≤ 4 + 4 :=
    le_add_of_nonneg_right hfour_nonneg
  exact
    Eq.subst
      (motive := fun x : ℝ => (4 : ℝ) ≤ x)
      hfour_add_four
      hle_sum

theorem Real.one_le_twenty_four :
    (1 : ℝ) ≤ 24 := by
  have hone_le_three : (1 : ℝ) ≤ 3 :=
    Real.one_le_three
  have hone_le_eight : (1 : ℝ) ≤ 8 :=
    le_trans one_le_two
      (le_trans Real.two_le_four_far_upper Real.four_le_eight_far_upper)
  have hthree_nonneg : (0 : ℝ) ≤ 3 :=
    le_trans zero_le_one hone_le_three
  have hmul_le :
      (1 : ℝ) * 1 ≤ 3 * 8 :=
    mul_le_mul hone_le_three hone_le_eight zero_le_one hthree_nonneg
  have hone_mul : (1 : ℝ) * 1 = 1 :=
    one_mul 1
  have htarget :
      (1 : ℝ) ≤ 3 * 8 :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ 3 * 8)
      hone_mul
      hmul_le
  exact
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      Real.three_mul_eight_eq_twenty_four
      htarget

theorem Real.four_add_four_eq_eight :
    (4 : ℝ) + 4 = 8 := by
  have hnat : (4 : ℕ) + 4 = 8 := by
    rfl
  calc
    (4 : ℝ) + 4 = (((4 : ℕ) + 4 : ℕ) : ℝ) := by
      exact (Nat.cast_add 4 4).symm
    _ = 8 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.four_mul_three_eq_twelve :
    (4 : ℝ) * 3 = 12 := by
  have hnat : (4 : ℕ) * 3 = 12 := by
    rfl
  calc
    (4 : ℝ) * 3 = (((4 : ℕ) * 3 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 4 3).symm
    _ = 12 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.one_le_twelve_far_upper :
    (1 : ℝ) ≤ 12 := by
  have hone_le_four : (1 : ℝ) ≤ 4 :=
    le_trans one_le_two Real.two_le_four_far_upper
  have hthree_nonneg : (0 : ℝ) ≤ 3 :=
    le_trans zero_le_one Real.one_le_three
  have hmul :
      (1 : ℝ) * 3 ≤ 4 * 3 :=
    mul_le_mul_of_nonneg_right hone_le_four hthree_nonneg
  have hone_mul : (1 : ℝ) * 3 = 3 :=
    one_mul 3
  have hthree_le_twelve :
      (3 : ℝ) ≤ 12 :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ 12)
      hone_mul
      (Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) * 3 ≤ x)
        Real.four_mul_three_eq_twelve
        hmul)
  exact le_trans Real.one_le_three hthree_le_twelve

theorem Real.twelve_mul_four_mul_two_eq_ninety_six :
    (12 : ℝ) * 4 * 2 = 96 := by
  have hnat : (12 * 4 * 2 : ℕ) = 96 := by
    rfl
  have hfirst :
      (12 : ℝ) * 4 = (((12 : ℕ) * 4 : ℕ) : ℝ) :=
    (Nat.cast_mul 12 4).symm
  have hsecond :
      (((12 : ℕ) * 4 : ℕ) : ℝ) * 2 =
        ((((12 : ℕ) * 4) * 2 : ℕ) : ℝ) :=
    (Nat.cast_mul ((12 : ℕ) * 4) 2).symm
  calc
    (12 : ℝ) * 4 * 2 =
        (((12 : ℕ) * 4 : ℕ) : ℝ) * 2 := by
      exact congrArg (fun x : ℝ => x * 2) hfirst
    _ = ((((12 : ℕ) * 4) * 2 : ℕ) : ℝ) := by
      exact hsecond
    _ = 96 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.twelve_mul_eight_eq_ninety_six :
    (12 : ℝ) * 8 = 96 := by
  have hnat : (12 : ℕ) * 8 = 96 := by
    rfl
  calc
    (12 : ℝ) * 8 = (((12 : ℕ) * 8 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 12 8).symm
    _ = 96 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.eight_mul_eight_eq_sixty_four :
    (8 : ℝ) * 8 = 64 := by
  have hnat : (8 : ℕ) * 8 = 64 := by
    rfl
  calc
    (8 : ℝ) * 8 = (((8 : ℕ) * 8 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 8 8).symm
    _ = 64 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.two_mul_ninety_six_eq_one_ninety_two :
    (2 : ℝ) * 96 = 192 := by
  have hnat : (2 : ℕ) * 96 = 192 := by
    rfl
  calc
    (2 : ℝ) * 96 = (((2 : ℕ) * 96 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 2 96).symm
    _ = 192 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.ninety_six_mul_two_eq_one_ninety_two :
    (96 : ℝ) * 2 = 192 := by
  have hnat : (96 : ℕ) * 2 = 192 := by
    rfl
  calc
    (96 : ℝ) * 2 = (((96 : ℕ) * 2 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 96 2).symm
    _ = 192 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.one_ninety_two_mul_sixty_four_eq_12288 :
    (192 : ℝ) * 64 = 12288 := by
  have hnat : (192 : ℕ) * 64 = 12288 := by
    rfl
  calc
    (192 : ℝ) * 64 = (((192 : ℕ) * 64 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 192 64).symm
    _ = 12288 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

theorem Real.zero_le_ninety_six :
    (0 : ℝ) ≤ 96 := by
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      Real.twelve_mul_eight_eq_ninety_six
      (mul_nonneg
        (le_trans zero_le_one Real.one_le_twelve_far_upper)
        Real.zero_le_eight)

theorem Real.zero_le_one_ninety_two :
    (0 : ℝ) ≤ 192 := by
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      Real.ninety_six_mul_two_eq_one_ninety_two
      (mul_nonneg Real.zero_le_ninety_six zero_le_two)

theorem Real.zero_le_12288 :
    (0 : ℝ) ≤ 12288 := by
  have hsixty_four_nonneg : (0 : ℝ) ≤ 64 :=
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      Real.eight_mul_eight_eq_sixty_four
      (mul_nonneg Real.zero_le_eight Real.zero_le_eight)
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      Real.one_ninety_two_mul_sixty_four_eq_12288
      (mul_nonneg Real.zero_le_one_ninety_two hsixty_four_nonneg)

theorem Real.one_sub_two_eq_neg_one :
    (1 : ℝ) - 2 = -1 := by
  have htwo : (2 : ℝ) = 1 + 1 :=
    one_add_one_eq_two.symm
  have hadd : (-1 : ℝ) + 2 = 1 := by
    calc
      (-1 : ℝ) + 2 = (-1 : ℝ) + (1 + 1) := by
        exact congrArg (fun x : ℝ => (-1 : ℝ) + x) htwo
      _ = ((-1 : ℝ) + 1) + 1 := by
        exact (add_assoc (-1 : ℝ) 1 1).symm
      _ = 0 + 1 := by
        exact congrArg (fun x : ℝ => x + 1) (neg_add_cancel 1)
      _ = 1 := by
        exact zero_add 1
  exact (sub_eq_iff_eq_add).mpr hadd.symm

theorem Real.one_sub_three_eq_neg_two :
    (1 : ℝ) - 3 = -2 := by
  have hthree : (3 : ℝ) = 2 + 1 :=
    Real.two_add_one_eq_three.symm
  have hadd : (-2 : ℝ) + 3 = 1 := by
    calc
      (-2 : ℝ) + 3 = (-2 : ℝ) + (2 + 1) := by
        exact congrArg (fun x : ℝ => (-2 : ℝ) + x) hthree
      _ = ((-2 : ℝ) + 2) + 1 := by
        exact (add_assoc (-2 : ℝ) 2 1).symm
      _ = 0 + 1 := by
        exact congrArg (fun x : ℝ => x + 1) (neg_add_cancel 2)
      _ = 1 := by
        exact zero_add 1
  exact (sub_eq_iff_eq_add).mpr hadd.symm

theorem Real.one_sub_five_eq_neg_four :
    (1 : ℝ) - 5 = -4 := by
  have hfive : (5 : ℝ) = 4 + 1 := by
    have hnat : (4 : ℕ) + 1 = 5 := by
      rfl
    calc
      (5 : ℝ) = (((4 : ℕ) + 1 : ℕ) : ℝ) := by
        exact (congrArg (fun n : ℕ => (n : ℝ)) hnat).symm
      _ = (4 : ℝ) + 1 := by
        have hright :
            ((4 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) =
              (4 : ℝ) + 1 :=
          congrArg₂ HAdd.hAdd
            (show ((4 : ℕ) : ℝ) = (4 : ℝ) by rfl)
            Nat.cast_one
        exact
          Eq.trans
            (Nat.cast_add 4 1)
            hright
  have hadd : (-4 : ℝ) + 5 = 1 := by
    calc
      (-4 : ℝ) + 5 = (-4 : ℝ) + (4 + 1) := by
        exact congrArg (fun x : ℝ => (-4 : ℝ) + x) hfive
      _ = ((-4 : ℝ) + 4) + 1 := by
        exact (add_assoc (-4 : ℝ) 4 1).symm
      _ = 0 + 1 := by
        exact congrArg (fun x : ℝ => x + 1) (neg_add_cancel 4)
      _ = 1 := by
        exact zero_add 1
  exact (sub_eq_iff_eq_add).mpr hadd.symm

theorem Real.two_pi_mul_five_div_eight_eq_five_pi_div_four_mul
    (N : ℝ) :
    ((2 : ℝ) * Real.pi) * ((5 * N) / 8) =
      ((5 * Real.pi) / 4) * N := by
  calc
    ((2 : ℝ) * Real.pi) * ((5 * N) / 8) =
        (((2 : ℝ) * Real.pi) * (5 * N)) / 8 := by
      exact (mul_div_assoc ((2 : ℝ) * Real.pi) (5 * N) 8).symm
    _ = (((2 : ℝ) * 5) * Real.pi * N) / 8 := by
      exact congrArg (fun x : ℝ => x / 8)
        (calc
          ((2 : ℝ) * Real.pi) * (5 * N) =
              2 * (Real.pi * (5 * N)) := by
            exact mul_assoc (2 : ℝ) Real.pi (5 * N)
          _ = 2 * ((Real.pi * 5) * N) := by
            exact congrArg (fun x : ℝ => 2 * x)
              (mul_assoc Real.pi 5 N).symm
          _ = 2 * ((5 * Real.pi) * N) := by
            exact congrArg (fun x : ℝ => 2 * (x * N))
              (mul_comm Real.pi 5)
          _ = (2 * (5 * Real.pi)) * N := by
            exact (mul_assoc (2 : ℝ) (5 * Real.pi) N).symm
          _ = ((2 * 5) * Real.pi) * N := by
            exact congrArg (fun x : ℝ => x * N)
              (mul_assoc (2 : ℝ) 5 Real.pi).symm)
    _ = ((10 * Real.pi) * N) / 8 := by
      exact congrArg (fun x : ℝ => (x * Real.pi * N) / 8)
        Real.two_mul_five_eq_ten
    _ = ((5 * Real.pi) * N) / 4 := by
      have htwo_ne : (2 : ℝ) ≠ 0 :=
        ne_of_gt zero_lt_two
      calc
        ((10 * Real.pi) * N) / 8 =
            ((2 * (5 * Real.pi)) * N) / (2 * 4) := by
          exact congrArg₂
            (fun x y : ℝ => (x * N) / y)
            (calc
              10 * Real.pi = (2 * 5) * Real.pi := by
                exact congrArg (fun x : ℝ => x * Real.pi)
                  Real.ten_eq_two_mul_five
              _ = 2 * (5 * Real.pi) := by
                exact mul_assoc (2 : ℝ) 5 Real.pi)
            Real.eight_eq_two_mul_four
        _ = ((5 * Real.pi) * N) / 4 := by
          have hnum_assoc :
              (2 * (5 * Real.pi)) * N =
                2 * ((5 * Real.pi) * N) :=
            mul_assoc (2 : ℝ) (5 * Real.pi) N
          exact Eq.trans
            (congrArg
              (fun x : ℝ => x / (2 * 4))
              hnum_assoc)
            (mul_div_mul_left ((5 * Real.pi) * N) 4 htwo_ne)
    _ = ((5 * Real.pi) / 4) * N := by
      exact (div_mul_eq_mul_div (5 * Real.pi) 4 N).symm

theorem Real.exp_two_pi_inv_le_five_pi_div_four_of_ge
    {t N : ℝ}
    (ht : (5 * N) / 8 ≤ t) :
    (Real.exp ((2 : ℝ) * Real.pi * t))⁻¹ ≤
      Real.exp (-((5 * Real.pi) / 4) * N) := by
  have hcoeff_nonneg :
      0 ≤ (2 : ℝ) * Real.pi :=
    le_of_lt (mul_pos two_pos Real.pi_pos)
  have hscaled :
      ((2 : ℝ) * Real.pi) * ((5 * N) / 8) ≤
        ((2 : ℝ) * Real.pi) * t :=
    mul_le_mul_of_nonneg_left ht hcoeff_nonneg
  have hneg :
      -(((2 : ℝ) * Real.pi) * t) ≤
        -(((2 : ℝ) * Real.pi) * ((5 * N) / 8)) :=
    neg_le_neg hscaled
  have hexp :
      Real.exp (-(((2 : ℝ) * Real.pi) * t)) ≤
        Real.exp (-(((2 : ℝ) * Real.pi) * ((5 * N) / 8))) :=
    Real.exp_le_exp.mpr hneg
  have hleft :
      (Real.exp ((2 : ℝ) * Real.pi * t))⁻¹ =
        Real.exp (-(((2 : ℝ) * Real.pi) * t)) := by
    calc
      (Real.exp ((2 : ℝ) * Real.pi * t))⁻¹ =
          Real.exp (-((2 : ℝ) * Real.pi * t)) := by
        exact (Real.exp_neg ((2 : ℝ) * Real.pi * t)).symm
      _ = Real.exp (-(((2 : ℝ) * Real.pi) * t)) := by
        exact Eq.refl (Real.exp (-(((2 : ℝ) * Real.pi) * t)))
  have hright :
      Real.exp (-(((2 : ℝ) * Real.pi) * ((5 * N) / 8))) =
        Real.exp (-((5 * Real.pi) / 4) * N) := by
    have hprod :
        Real.exp (-(((2 : ℝ) * Real.pi) * ((5 * N) / 8))) =
          Real.exp (-(((5 * Real.pi) / 4) * N)) :=
      congrArg (fun x : ℝ => Real.exp (-x))
        (Real.two_pi_mul_five_div_eight_eq_five_pi_div_four_mul N)
    have hneg_mul :
        -(((5 * Real.pi) / 4) * N) =
          -((5 * Real.pi) / 4) * N :=
      (neg_mul ((5 * Real.pi) / 4) N).symm
    exact Eq.trans hprod (congrArg Real.exp hneg_mul)
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤ Real.exp (-((5 * Real.pi) / 4) * N))
      hleft.symm
      (Eq.subst
        (motive := fun x : ℝ =>
          Real.exp (-(((2 : ℝ) * Real.pi) * t)) ≤ x)
        hright
        hexp)

theorem Complex.abs_im_le_norm_owner
    (w : ℂ) :
    |w.im| ≤ ‖w‖ :=
  Eq.subst
    (motive := fun x : ℝ => |w.im| ≤ x)
    (Complex.norm_eq_abs w).symm
    (Complex.abs_im_le_abs w)

theorem Set.Ioc_subset_Icc_same
    {a b : ℝ} :
    Set.Ioc a b ⊆ Set.Icc a b :=
  Set.Ioc_subset_Icc_self

end

end LFunctions
end Boundary
