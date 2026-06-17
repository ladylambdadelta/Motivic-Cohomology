import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaEndpointCapCollars

/-!
# Interior cap-collar Cauchy balances for finite Abel-Plana

This file owns the interior deleted-disk collar balances and their assembly with
endpoint cap-collar balances into the finite-hole subdivision boundary
cancellation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Interior horizontal subdivision index bound used by the collar split. -/
theorem Nat.finiteAbelPlana_two_mul_succ_lt_two_mul_add_three_of_lt
    {n N : ℕ}
    (hn : n < N) :
    2 * (n + 1) < 2 * N + 3 := by
  have hsucc_le : n + 1 ≤ N :=
    Nat.succ_le_iff.mpr hn
  have hmul_le : 2 * (n + 1) ≤ 2 * N :=
    Nat.mul_le_mul_left 2 hsucc_le
  have htail_lt : 2 * N < 2 * N + 3 :=
    Nat.lt_add_of_pos_right (Nat.succ_pos 2)
  exact Nat.lt_of_le_of_lt hmul_le htail_lt

/-- Reassociate three additive terms by moving the middle term to the front. -/
theorem Complex.add_left_middle_right (a b c : ℂ) :
    (a + b) + c = b + (a + c) := by
  calc
    (a + b) + c = (b + a) + c :=
      congrArg (fun x : ℂ => x + c) (add_comm a b)
    _ = b + (a + c) :=
      add_assoc b a c

/-- The circle derivative for a real radius may be written with `I` first. -/
theorem Complex.circle_derivative_real_radius_commute
    (ρ : ℝ)
    (θ : ℝ) :
    (ρ : ℂ) * (Complex.I * Complex.exp (Complex.I * (θ : ℂ))) =
      Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
  calc
    (ρ : ℂ) * (Complex.I * Complex.exp (Complex.I * (θ : ℂ))) =
        ((ρ : ℂ) * Complex.I) * Complex.exp (Complex.I * (θ : ℂ)) :=
      (mul_assoc (ρ : ℂ) Complex.I (Complex.exp (Complex.I * (θ : ℂ)))).symm
    _ = (Complex.I * (ρ : ℂ)) * Complex.exp (Complex.I * (θ : ℂ)) :=
      congrArg
        (fun z : ℂ => z * Complex.exp (Complex.I * (θ : ℂ)))
        (mul_comm (ρ : ℂ) Complex.I)
    _ = Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) :=
      rfl

/-- Real part of subtracting a natural-number point on the real axis. -/
theorem Complex.sub_natCast_re
    (z : ℂ)
    (m : ℕ) :
    (z - (m : ℂ)).re = z.re - (m : ℝ) := by
  calc
    (z - (m : ℂ)).re = z.re - ((m : ℂ).re) :=
      Complex.sub_re z (m : ℂ)
    _ = z.re - (m : ℝ) := rfl

/-- Imaginary part of subtracting a natural-number point on the real axis. -/
theorem Complex.sub_natCast_im
    (z : ℂ)
    (m : ℕ) :
    (z - (m : ℂ)).im = z.im := by
  calc
    (z - (m : ℂ)).im = z.im - ((m : ℂ).im) :=
      Complex.sub_im z (m : ℂ)
    _ = z.im - 0 := rfl
    _ = z.im := sub_zero z.im

/-- Real part of a complex norm controls the norm. -/
theorem Complex.abs_re_le_norm
    (z : ℂ) :
    |z.re| ≤ ‖z‖ := by
  exact (Complex.norm_eq_abs z).symm ▸ Complex.abs_re_le_abs z

/-- Imaginary part of a complex norm controls the norm. -/
theorem Complex.abs_im_le_norm
    (z : ℂ) :
    |z.im| ≤ ‖z‖ := by
  exact (Complex.norm_eq_abs z).symm ▸ Complex.abs_im_le_abs z

/-- A nonnegative radius orders the closed interval centered at `x`. -/
theorem Real.interior_center_sub_radius_le_add_radius
    (x ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    x - ρ ≤ x + ρ := by
  exact (sub_le_self x hρ).trans (le_add_of_nonneg_right hρ)

/-- A radius bounded by one keeps the right edge of an interior collar before
the next unit-spaced endpoint. -/
theorem Real.interior_succ_add_radius_le_next_succ
    {n N : ℕ}
    {ρ : ℝ}
    (hn : n + 1 ≤ N)
    (hρ : ρ ≤ 1) :
    ((n + 1 : ℕ) : ℝ) + ρ ≤ ((N + 1 : ℕ) : ℝ) := by
  have hn_real : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) :=
    Real.natCast_le_natCast hn
  have hsum : ((n + 1 : ℕ) : ℝ) + ρ ≤ (N : ℝ) + 1 :=
    add_le_add hn_real hρ
  exact hsum.trans_eq (Real.natCast_succ_eq N).symm

/-- Absolute-value control around a center gives membership in the centered
closed interval. -/
theorem Real.mem_centered_Icc_of_abs_sub_le
    {x c ρ : ℝ}
    (h : |x - c| ≤ ρ) :
    x ∈ Set.Icc (c - ρ) (c + ρ) := by
  have hbounds : -ρ ≤ x - c ∧ x - c ≤ ρ :=
    abs_le.mp h
  have hleft : c - ρ ≤ x := by
    have hraw : -ρ + c ≤ x :=
      le_sub_iff_add_le.mp hbounds.1
    calc
      c - ρ = c + -ρ := sub_eq_add_neg c ρ
      _ = -ρ + c := add_comm c (-ρ)
      _ ≤ x := hraw
  have hright : x ≤ c + ρ := by
    have hraw : x ≤ ρ + c :=
      sub_le_iff_le_add.mp hbounds.2
    exact hraw.trans_eq (add_comm ρ c)
  exact ⟨hleft, hright⟩

/-- If a collar radius is at most one half, then it is no larger than the
remaining unit gap after deleting another copy of that radius. -/
theorem Real.interior_radius_le_one_sub_radius_of_le_half
    {ρ : ℝ}
    (hρhalf : ρ ≤ (1 : ℝ) / 2) :
    ρ ≤ 1 - ρ := by
  have hdouble : ρ + ρ ≤ (1 : ℝ) := by
    exact (add_le_add hρhalf hρhalf).trans_eq (add_halves (1 : ℝ))
  exact le_sub_iff_add_le.mpr hdouble

/-- A point in the left half of the collar around `n + 1` is at least `ρ`
to the right of every integer `m ≤ n`, provided `ρ ≤ 1 - ρ`. -/
theorem Real.interior_left_gap_from_previous_integer
    {x ρ : ℝ}
    {m n : ℕ}
    (hmn : m ≤ n)
    (hleft : ((n + 1 : ℕ) : ℝ) - ρ ≤ x)
    (hρgap : ρ ≤ 1 - ρ) :
    ρ ≤ x - (m : ℝ) := by
  have hm_succ_le : m + 1 ≤ n + 1 :=
    Nat.succ_le_succ hmn
  have hone_gap : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) - (m : ℝ) := by
    have hraw : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
      Real.natCast_le_natCast hm_succ_le
    have hsucc : (((m + 1 : ℕ) : ℝ) : ℝ) = (m : ℝ) + 1 :=
      Real.natCast_succ_eq m
    have hcast : (m : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) :=
      hsucc ▸ hraw
    exact le_sub_iff_add_le.mpr hcast
  have hgap : 1 - ρ ≤ ((n + 1 : ℕ) : ℝ) - ρ - (m : ℝ) := by
    have hshift : (1 : ℝ) - ρ ≤ (((n + 1 : ℕ) : ℝ) - (m : ℝ)) - ρ :=
      sub_le_sub_right hone_gap ρ
    exact hshift.trans_eq (sub_sub (((n + 1 : ℕ) : ℝ)) ρ (m : ℝ)).symm
  have hpoint : ((n + 1 : ℕ) : ℝ) - ρ - (m : ℝ) ≤ x - (m : ℝ) :=
    sub_le_sub_right hleft (m : ℝ)
  exact hρgap.trans (hgap.trans hpoint)

/-- A point in the right half of the collar around `n + 1` is at least `ρ`
to the left of every integer `m ≥ n + 2`, provided `ρ ≤ 1 - ρ`. -/
theorem Real.interior_right_gap_from_later_integer
    {x ρ : ℝ}
    {m n : ℕ}
    (hnm : n + 2 ≤ m)
    (hright : x ≤ ((n + 1 : ℕ) : ℝ) + ρ)
    (hρgap : ρ ≤ 1 - ρ) :
    x - (m : ℝ) ≤ -ρ := by
  have hnext_le : ((n + 2 : ℕ) : ℝ) ≤ (m : ℝ) :=
    Real.natCast_le_natCast hnm
  have hsucc : (((n + 2 : ℕ) : ℝ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 :=
    Real.natCast_succ_eq (n + 1)
  have hone_le_gap : ((n + 1 : ℕ) : ℝ) + 1 ≤ (m : ℝ) :=
    hsucc ▸ hnext_le
  have htop : x ≤ (m : ℝ) - (1 - ρ) := by
    have htarget : ((n + 1 : ℕ) : ℝ) + ρ ≤ (m : ℝ) - (1 - ρ) := by
      have hsum_le : ((n + 1 : ℕ) : ℝ) + ρ + (1 - ρ) ≤ (m : ℝ) := by
        have hρsum : ρ + (1 - ρ) ≤ 1 := by
          exact le_sub_iff_add_le.mp hρgap
        calc
          ((n + 1 : ℕ) : ℝ) + ρ + (1 - ρ) =
              ((n + 1 : ℕ) : ℝ) + (ρ + (1 - ρ)) :=
            add_assoc (((n + 1 : ℕ) : ℝ)) ρ (1 - ρ)
          _ ≤ ((n + 1 : ℕ) : ℝ) + 1 :=
            add_le_add_left hρsum (((n + 1 : ℕ) : ℝ))
          _ ≤ (m : ℝ) :=
            hone_le_gap
      exact le_sub_iff_add_le.mpr hsum_le
    exact hright.trans htarget
  have hsub : x - (m : ℝ) ≤ -(1 - ρ) := by
    exact sub_le_iff_le_add.mpr
      (htop.trans_eq (by
        calc
          (m : ℝ) - (1 - ρ) = -(1 - ρ) + (m : ℝ) := by
            exact (sub_eq_add_neg (m : ℝ) (1 - ρ)).trans (add_comm (m : ℝ) (-(1 - ρ)))
          _ = -(1 - ρ) + (m : ℝ) :=
            rfl))
  have hneg : -(1 - ρ) ≤ -ρ :=
    neg_le_neg hρgap
  exact hsub.trans hneg

/-- Half of a positive real number is strictly smaller than the number. -/
theorem Real.half_lt_self_of_pos {x : ℝ} (hx : 0 < x) :
    x / 2 < x := by
  have hdouble : x / 2 + x / 2 < x / 2 + x := by
    exact add_lt_add_left hx (x / 2)
  exact (add_halves x).symm.trans_lt hdouble

/-- The left edge of an interior collar lies before its center. -/
theorem Real.interior_verticalStripRight_le_center
    (n : ℕ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    Complex.finiteAbelPlanaVerticalStripRight n ρ ≤ ((n + 1 : ℕ) : ℝ) := by
  exact sub_le_self (((n + 1 : ℕ) : ℝ)) hρ

/-- The center of an interior collar lies before its right edge. -/
theorem Real.interior_center_le_verticalStripLeft
    (n : ℕ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ((n + 1 : ℕ) : ℝ) ≤
      Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ := by
  exact le_add_of_nonneg_right hρ

/-- The left half of an interior collar is contained in the full collar
horizontal interval. -/
theorem Real.interior_left_half_subset_full_interval
    (n : ℕ)
    {ρ x : ℝ}
    (hρ : 0 ≤ ρ)
    (hx :
      x ∈ Set.Icc
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (((n + 1 : ℕ) : ℝ))) :
    x ∈ Set.Icc
      (Complex.finiteAbelPlanaVerticalStripRight n ρ)
      (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ) := by
  exact
    ⟨hx.1,
      hx.2.trans (Real.interior_center_le_verticalStripLeft n hρ)⟩

/-- The right half of an interior collar is contained in the full collar
horizontal interval. -/
theorem Real.interior_right_half_subset_full_interval
    (n : ℕ)
    {ρ x : ℝ}
    (hρ : 0 ≤ ρ)
    (hx :
      x ∈ Set.Icc
        (((n + 1 : ℕ) : ℝ))
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)) :
    x ∈ Set.Icc
      (Complex.finiteAbelPlanaVerticalStripRight n ρ)
      (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ) := by
  exact
    ⟨(Real.interior_verticalStripRight_le_center n hρ).trans hx.1,
      hx.2⟩

/-- The left half of an interior collar is contained in the full collar
horizontal unoriented interval. -/
theorem Real.interior_left_half_subset_full_uIcc
    (n : ℕ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    [[Complex.finiteAbelPlanaVerticalStripRight n ρ, ((n + 1 : ℕ) : ℝ)]] ⊆
      [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
        Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] := by
  intro x hx
  have hright_order :
      Complex.finiteAbelPlanaVerticalStripRight n ρ ≤ ((n + 1 : ℕ) : ℝ) :=
    Real.interior_verticalStripRight_le_center n hρ
  have hxIcc :
      x ∈ Set.Icc
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (((n + 1 : ℕ) : ℝ)) :=
    (Set.uIcc_of_le hright_order) ▸ hx
  have hwhole_order :
      Complex.finiteAbelPlanaVerticalStripRight n ρ ≤
        Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ :=
    Real.interior_center_sub_radius_le_add_radius
      (((n + 1 : ℕ) : ℝ)) ρ hρ
  have hfull :
      x ∈ Set.Icc
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ) :=
    Real.interior_left_half_subset_full_interval n hρ hxIcc
  exact (Set.uIcc_of_le hwhole_order).symm ▸ hfull

/-- The right half of an interior collar is contained in the full collar
horizontal unoriented interval. -/
theorem Real.interior_right_half_subset_full_uIcc
    (n : ℕ)
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    [[((n + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] ⊆
      [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
        Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] := by
  intro x hx
  have hright_order :
      ((n + 1 : ℕ) : ℝ) ≤
        Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ :=
    Real.interior_center_le_verticalStripLeft n hρ
  have hxIcc :
      x ∈ Set.Icc
        (((n + 1 : ℕ) : ℝ))
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ) :=
    (Set.uIcc_of_le hright_order) ▸ hx
  have hwhole_order :
      Complex.finiteAbelPlanaVerticalStripRight n ρ ≤
        Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ :=
    Real.interior_center_sub_radius_le_add_radius
      (((n + 1 : ℕ) : ℝ)) ρ hρ
  have hfull :
      x ∈ Set.Icc
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ) :=
    Real.interior_right_half_subset_full_interval n hρ hxIcc
  exact (Set.uIcc_of_le hwhole_order).symm ▸ hfull

/-- Adding one full turn carries `-π/2` to `3π/2`. -/
theorem Real.neg_pi_div_two_add_two_pi_eq_three_pi_div_two :
    -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2 := by
  have hthree :
      (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by
    calc
      (3 : ℝ) * Real.pi / 2 =
          (Real.pi + Real.pi + Real.pi) / 2 := by
        exact congrArg (fun z : ℝ => z / 2) (three_mul Real.pi)
      _ = (Real.pi + Real.pi) / 2 + Real.pi / 2 := by
        exact add_div (Real.pi + Real.pi) Real.pi 2
      _ = Real.pi + Real.pi / 2 := by
        exact congrArg (fun z : ℝ => z + Real.pi / 2) (add_halves Real.pi)
  calc
    -(Real.pi / 2) + 2 * Real.pi =
        2 * Real.pi - Real.pi / 2 := by
      exact
        (add_comm (-(Real.pi / 2)) (2 * Real.pi)).trans
          (sub_eq_add_neg (2 * Real.pi) (Real.pi / 2)).symm
    _ = Real.pi + Real.pi / 2 := by
      have htwo : 2 * Real.pi = Real.pi + Real.pi :=
        two_mul Real.pi
      calc
        2 * Real.pi - Real.pi / 2 =
            (Real.pi + Real.pi) - Real.pi / 2 := by
          exact congrArg (fun z : ℝ => z - Real.pi / 2) htwo
        _ = Real.pi + (Real.pi - Real.pi / 2) := by
          exact (add_sub_assoc Real.pi Real.pi (Real.pi / 2)).symm
        _ = Real.pi + Real.pi / 2 := by
          exact congrArg (fun z : ℝ => Real.pi + z) (sub_eq_iff_eq_add.mpr (add_halves Real.pi).symm)
    _ = 3 * Real.pi / 2 :=
      hthree.symm

/-- Adding one full turn fixes the zero angle endpoint. -/
theorem Real.zero_add_two_pi_eq_two_pi :
    (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by
  exact zero_add (2 * Real.pi)

/-- Subtracting one full turn carries `3π/2` to `-π/2`. -/
theorem Real.three_pi_div_two_sub_two_pi_eq_neg_pi_div_two :
    3 * Real.pi / 2 - 2 * Real.pi = -(Real.pi / 2) := by
  exact sub_eq_iff_eq_add.mpr Real.neg_pi_div_two_add_two_pi_eq_three_pi_div_two.symm

/-- Subtracting one full turn carries `2π` to `0`. -/
theorem Real.two_pi_sub_two_pi_eq_zero :
    2 * Real.pi - 2 * Real.pi = (0 : ℝ) := by
  exact sub_self (2 * Real.pi)

/-- The complex exponential argument after one real angular period is the old
argument plus `2πI`. -/
theorem Complex.I_mul_ofReal_add_two_pi
    (θ : ℝ) :
    Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ) =
      Complex.I * (θ : ℂ) + (2 * Real.pi * Complex.I) := by
  calc
    Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ) =
        Complex.I * ((θ : ℂ) + ((2 * Real.pi : ℝ) : ℂ)) := by
      exact congrArg (fun z : ℂ => Complex.I * z) (Complex.ofReal_add θ (2 * Real.pi))
    _ = Complex.I * (θ : ℂ) + Complex.I * ((2 * Real.pi : ℝ) : ℂ) := by
      exact mul_add Complex.I (θ : ℂ) ((2 * Real.pi : ℝ) : ℂ)
    _ = Complex.I * (θ : ℂ) + (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
      exact congrArg
        (fun z : ℂ => Complex.I * (θ : ℂ) + z)
        (mul_comm Complex.I (((2 * Real.pi : ℝ) : ℂ)))
    _ = Complex.I * (θ : ℂ) + (2 * Real.pi * Complex.I) := by
      rfl

/-- The interior deleted-circle parametrization is mathlib's `circleMap`
parametrization, with the exponential argument commuted into the convention
used by `circleMap`. -/
theorem Complex.finiteAbelPlana_interiorCircleParam_eq_circleMap
    (n : ℕ)
    (ρ θ : ℝ) :
    (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      circleMap (n + 1 : ℂ) ρ θ := by
  calc
    (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        ((n + 1 : ℂ) + (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
      exact
        congrArg
          (fun z : ℂ => (n + 1 : ℂ) + (ρ : ℂ) * Complex.exp z)
          (mul_comm Complex.I (θ : ℂ))
    _ = circleMap (n + 1 : ℂ) ρ θ :=
      rfl

/-- Membership in the local left half-domain at an interior integer, unfolded
only to its geometric components. -/
theorem Complex.mem_leftHalfRectangleDeletedDiskDomain_interiorInteger_iff
    (n : ℕ)
    (T ρ : ℝ)
    (z : ℂ) :
    z ∈ Complex.leftHalfRectangleDeletedDiskDomain (n + 1 : ℂ) T ρ ρ ↔
      (z.re ∈ [[((n + 1 : ℕ) : ℝ) - ρ, ((n + 1 : ℕ) : ℝ)]] ∧
        z.im ∈ [[-T, T]]) ∧
        z ∉ Metric.ball (n + 1 : ℂ) ρ := by
  rfl

/-- Membership in the local right half-domain at an interior integer, unfolded
only to its geometric components. -/
theorem Complex.mem_rightHalfRectangleDeletedDiskDomain_interiorInteger_iff
    (n : ℕ)
    (T ρ : ℝ)
    (z : ℂ) :
    z ∈ Complex.rightHalfRectangleDeletedDiskDomain (n + 1 : ℂ) T ρ ρ ↔
      (z.re ∈ [[((n + 1 : ℕ) : ℝ), ((n + 1 : ℕ) : ℝ) + ρ]] ∧
        z.im ∈ [[-T, T]]) ∧
        z ∉ Metric.ball (n + 1 : ℂ) ρ := by
  rfl

/-- The oriented boundary integral of the punctured interior collar around the
deleted disk centered at `n + 1`, before the residue normalization factor is
applied.

The four straight sides are the two horizontal collars and the two adjacent
safe-strip vertical sides.  The last term is the clockwise inner boundary of the
deleted disk, written as the negative of the standard counterclockwise
`circleIntegral`. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
      Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
        Complex.I *
          Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
          Complex.I *
            Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
          circleIntegral
            (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
            (n + 1 : ℂ)
            ρ

/-- Unfolding of the punctured interior collar boundary into its four straight
collar sides and clockwise deleted-circle side. -/
theorem Complex.finiteAbelPlana_log_interiorCapCollarPuncturedBoundary_unfold
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary n w T ρ =
      Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
          Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I *
                Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
              circleIntegral
                (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
                (n + 1 : ℂ)
                ρ := by
  rfl

/-- The interior cap/collar boundary is the canonical punctured rectangular
collar boundary for the rectangle
`[(n+1)-ρ, (n+1)+ρ] × [-T,T]` with the disk centered at `n+1` removed. -/
theorem Complex.finiteAbelPlana_log_interiorCapCollarPuncturedBoundary_eq_puncturedRectangularCollarBoundary
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary n w T ρ =
      Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary
        w
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
        T
        (n + 1 : ℂ)
        ρ := by
  rfl

/-- The closed rectangle underlying the interior collar around `n + 1` lies in
the ambient finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogInteriorCollarClosedRectangle_subset_closedRectangle
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    ({z : ℂ |
        z.re ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
          Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] ∧
        z.im ∈ [[-T, T]]} : Set ℂ) ⊆
      Complex.finiteAbelPlanaClosedRectangle N T := by
  intro z hz
  have hn_lt : n < N := Finset.mem_range.mp hn
  have hn_succ_le : n + 1 ≤ N := Nat.succ_le_iff.mpr hn_lt
  have hρ_lt_one : ρ < 1 :=
    Real.lt_one_of_lt_one_div_four hρquarter
  have hleft_nonneg :
      0 ≤ Complex.finiteAbelPlanaVerticalStripRight n ρ := by
    have hone_le : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact Real.one_le_natCast_succ n
    exact sub_nonneg.mpr ((le_of_lt hρ_lt_one).trans hone_le)
  have hright_le :
      Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ ≤ ((N + 1 : ℕ) : ℝ) := by
    have hn_succ_real : (((n + 1 : ℕ) : ℝ) : ℝ) ≤ (N : ℝ) := by
      exact Real.natCast_le_natCast hn_succ_le
    have hρ_le_one : ρ ≤ 1 :=
      le_of_lt hρ_lt_one
    exact Real.interior_succ_add_radius_le_next_succ hn_succ_le hρ_le_one
  have hleft_le_right :
      Complex.finiteAbelPlanaVerticalStripRight n ρ ≤
        Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ := by
    exact
      Real.interior_center_sub_radius_le_add_radius
        (((n + 1 : ℕ) : ℝ)) ρ hρnonneg
  have hre_interval :
      z.re ∈ Set.Icc
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ) := by
    exact (Set.uIcc_of_le hleft_le_right) ▸ hz.1
  exact ⟨⟨hleft_nonneg.trans hre_interval.1, hre_interval.2.trans hright_le⟩, hz.2⟩

/-- The closed deleted disk in the interior collar lies in the collar's closed
rectangle when the radius fits inside the finite height. -/
theorem Complex.finiteAbelPlanaLogInteriorCollarClosedDisk_subset_closedRectangle
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hρnonneg : 0 ≤ ρ)
    (hρheight : ρ ≤ |T|) :
    Metric.closedBall (n + 1 : ℂ) ρ ⊆
      ({z : ℂ |
          z.re ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] ∧
          z.im ∈ [[-T, T]]} : Set ℂ) := by
  intro z hz
  have hdist : ‖z - (n + 1 : ℂ)‖ ≤ ρ := by
    exact (dist_eq_norm z (n + 1 : ℂ)) ▸ Metric.mem_closedBall.mp hz
  have hre_norm :
      |(z - (n + 1 : ℂ)).re| ≤ ‖z - (n + 1 : ℂ)‖ := by
    exact Complex.abs_re_le_norm (z - (n + 1 : ℂ))
  have him_norm :
      |(z - (n + 1 : ℂ)).im| ≤ ‖z - (n + 1 : ℂ)‖ := by
    exact Complex.abs_im_le_norm (z - (n + 1 : ℂ))
  have hre_abs : |z.re - ((n + 1 : ℕ) : ℝ)| ≤ ρ := by
    have hraw : |(z - (n + 1 : ℂ)).re| ≤ ρ :=
      hre_norm.trans hdist
    exact (congrArg (fun r : ℝ => |r| ≤ ρ)
      (Complex.sub_natCast_re z (n + 1))) ▸ hraw
  have him_abs : |z.im| ≤ ρ := by
    have hraw : |(z - (n + 1 : ℂ)).im| ≤ ρ :=
      him_norm.trans hdist
    exact (congrArg (fun r : ℝ => |r| ≤ ρ)
      (Complex.sub_natCast_im z (n + 1))) ▸ hraw
  have hre_bounds := abs_le.mp hre_abs
  have hre_mem :
      z.re ∈
        [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
          Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] := by
    exact
      Set.mem_uIcc_of_le
        (Real.mem_centered_Icc_of_abs_sub_le hre_abs).1
        (Real.mem_centered_Icc_of_abs_sub_le hre_abs).2
  have him_abs_height : |z.im| ≤ |T| :=
    him_abs.trans hρheight
  have him_mem : z.im ∈ [[-T, T]] := by
    by_cases hTnonneg : 0 ≤ T
    · have hT_abs : |T| = T := abs_of_nonneg hTnonneg
      have him_abs_to_T : |z.im| ≤ T :=
        hT_abs ▸ him_abs_height
      have him_bounds := abs_le.mp him_abs_to_T
      exact Set.mem_uIcc_of_le him_bounds.1 him_bounds.2
    · have hTnonpos : T ≤ 0 := le_of_not_ge hTnonneg
      have hT_abs : |T| = -T := abs_of_nonpos hTnonpos
      have him_abs_to_negT : |z.im| ≤ -T :=
        hT_abs ▸ him_abs_height
      have him_bounds := abs_le.mp him_abs_to_negT
      exact Set.mem_uIcc_of_ge him_bounds.1 him_bounds.2
  exact ⟨hre_mem, him_mem⟩

/-- A point in the interior collar rectangle, after deleting its own central
disk, avoids every listed deleted integer disk. -/
theorem Complex.finiteAbelPlanaLogInteriorCollarPoint_not_mem_deletedDisk
    {N m : ℕ}
    {T ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (_hm : m ∈ Finset.range (N + 2))
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    {z : ℂ}
    (hzre :
      z.re ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
        Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]])
    (_hzim : z.im ∈ [[-T, T]])
    (hzcentral : z ∉ Metric.ball (n + 1 : ℂ) ρ) :
    z ∉ Metric.ball (m : ℂ) ρ := by
  by_cases hmcenter : m = n + 1
  · subst m
    exact hzcentral
  · intro hzball
    have hleft_le_right :
        Complex.finiteAbelPlanaVerticalStripRight n ρ ≤
          Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ := by
      exact
        Real.interior_center_sub_radius_le_add_radius
          (((n + 1 : ℕ) : ℝ)) ρ hρnonneg
    have hzIcc :
        z.re ∈ Set.Icc
          (Complex.finiteAbelPlanaVerticalStripRight n ρ)
          (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ) := by
      exact (Set.uIcc_of_le hleft_le_right) ▸ hzre
    have hdist_lt : ‖z - (m : ℂ)‖ < ρ := by
      exact (dist_eq_norm z (m : ℂ)) ▸ Metric.mem_ball.mp hzball
    have hre_norm :
        |(z - (m : ℂ)).re| ≤ ‖z - (m : ℂ)‖ := by
      exact Complex.abs_re_le_norm (z - (m : ℂ))
    have hρ_le_one_sub : ρ ≤ 1 - ρ := by
      exact
        Real.interior_radius_le_one_sub_radius_of_le_half
          (le_of_lt (Real.lt_one_div_two_of_lt_one_div_four hρquarter))
    by_cases hm_le_n : m ≤ n
    · have hm_le_n_real : ((m : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact Real.natCast_le_natCast hm_le_n
      have hleft : Complex.finiteAbelPlanaVerticalStripRight n ρ ≤ z.re :=
        hzIcc.1
      have hre_ge : ρ ≤ (z - (m : ℂ)).re := by
        have hleft_real : ((n + 1 : ℕ) : ℝ) - ρ ≤ z.re := by
          exact hleft
        have hgap : ρ ≤ z.re - (m : ℝ) :=
          Real.interior_left_gap_from_previous_integer
            hm_le_n hleft_real hρ_le_one_sub
        exact (Complex.sub_natCast_re z m).symm ▸ hgap
      have hρ_le_abs : ρ ≤ |(z - (m : ℂ)).re| :=
        hre_ge.trans (le_abs_self _)
      exact not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt
    · have hn_lt_m : n < m := Nat.lt_of_not_ge hm_le_n
      have hn_succ_le_m : n + 1 ≤ m := Nat.succ_le_iff.mpr hn_lt_m
      have hn_succ_lt_m : n + 1 < m := by
        exact Nat.lt_of_le_of_ne hn_succ_le_m (Ne.symm hmcenter)
      have hn_two_le_m : n + 2 ≤ m := Nat.succ_le_iff.mpr hn_succ_lt_m
      have hn_two_le_m_real : (((n + 2 : ℕ) : ℝ) : ℝ) ≤ (m : ℝ) := by
        exact Real.natCast_le_natCast hn_two_le_m
      have hright : z.re ≤ Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ :=
        hzIcc.2
      have hre_le_neg : (z - (m : ℂ)).re ≤ -ρ := by
        have hright_real : z.re ≤ ((n + 1 : ℕ) : ℝ) + ρ := by
          exact hright
        have hgap : z.re - (m : ℝ) ≤ -ρ :=
          Real.interior_right_gap_from_later_integer
            hn_two_le_m hright_real hρ_le_one_sub
        exact (Complex.sub_natCast_re z m).symm ▸ hgap
      have hρ_le_abs : ρ ≤ |(z - (m : ℂ)).re| := by
        have hneg : ρ ≤ -((z - (m : ℂ)).re) := by
          exact neg_le_comm.mp hre_le_neg
        exact hneg.trans (neg_le_abs _)
      exact not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt

/-- The punctured rectangular collar around the interior pole `n + 1` is a
subset of the finite Abel-Plana punctured rectangle. -/
theorem Complex.finiteAbelPlanaLogInteriorPuncturedRectangularCollar_subset_puncturedRectangle
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogPuncturedRectangularCollar
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
        T
        (n + 1 : ℂ)
        ρ ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  exact
    Complex.finiteAbelPlanaLogPuncturedRectangularCollar_subset_puncturedRectangle
      (Complex.finiteAbelPlanaLogInteriorCollarClosedRectangle_subset_closedRectangle
        T n hn hρnonneg hρquarter)
      (fun z hzre hzim hzcentral m hm =>
        Complex.finiteAbelPlanaLogInteriorCollarPoint_not_mem_deletedDisk
          n hn hm hρnonneg hρquarter hzre hzim hzcentral)

/-- The vertical diameter used as the shared internal edge when the full
interior collar is split into left and right semicollars. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorCollarVerticalDiameter
    (n : ℕ)
    (w : ℂ)
    (T : ℝ) : ℂ :=
  ∫ y : ℝ in (-T)..T,
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      (((n + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ))

/-- Lower horizontal side of the left interior semicollar. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ x : ℝ in (Complex.finiteAbelPlanaVerticalStripRight n ρ)..((n + 1 : ℕ) : ℝ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) - Complex.I * (T : ℂ))

/-- Lower horizontal side of the right interior semicollar. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ x : ℝ in ((n + 1 : ℕ) : ℝ)..(Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) - Complex.I * (T : ℂ))

/-- Upper horizontal side of the left interior semicollar. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ x : ℝ in (Complex.finiteAbelPlanaVerticalStripRight n ρ)..((n + 1 : ℕ) : ℝ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (T : ℂ))

/-- Upper horizontal side of the right interior semicollar. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  ∫ x : ℝ in ((n + 1 : ℕ) : ℝ)..(Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
      ((x : ℂ) + Complex.I * (T : ℂ))

/-- Counterclockwise left semicircle around the interior deleted disk. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral
    (n : ℕ)
    (w : ℂ)
    (ρ : ℝ) : ℂ :=
  ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Counterclockwise right semicircle around the interior deleted disk, split
at angle `0` so that it concatenates directly with mathlib's `0..2π`
`circleIntegral` parametrization. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral
    (n : ℕ)
    (w : ℂ)
    (ρ : ℝ) : ℂ :=
  (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) +
    ∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Oriented boundary of the left interior semicollar.  The final term is the
clockwise deleted-boundary contribution, written as minus the counterclockwise
left semicircle. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ -
      Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar n w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogInteriorCollarVerticalDiameter n w T -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
          Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral n w ρ

/-- Oriented boundary of the right interior semicollar.  The internal vertical
diameter is oriented oppositely to the left semicollar and cancels in the sum. -/
noncomputable def Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ -
      Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar n w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogInteriorCollarVerticalDiameter n w T -
          Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ

/-- Lower interior collar split across the vertical diameter through the
deleted integer.  This is only interval concatenation on the lower horizontal
side. -/
theorem Complex.finiteAbelPlana_log_interiorLowerCollar_eq_left_add_right
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) - Complex.I * (T : ℂ)))
        volume
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (((n + 1 : ℕ) : ℝ)))
    (hright :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) - Complex.I * (T : ℂ)))
        volume
        (((n + 1 : ℕ) : ℝ))
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)) :
    Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ =
      Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
        Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ := by
  exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

/-- Upper interior collar split across the vertical diameter through the
deleted integer.  This is the upper horizontal analogue of the lower split. -/
theorem Complex.finiteAbelPlana_log_interiorUpperCollar_eq_left_add_right
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + Complex.I * (T : ℂ)))
        volume
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (((n + 1 : ℕ) : ℝ)))
    (hright :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + Complex.I * (T : ℂ)))
        volume
        (((n + 1 : ℕ) : ℝ))
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)) :
    Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ =
      Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar n w T ρ +
        Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar n w T ρ := by
  exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

/-- The `circleIntegral` parametrization around an interior deleted disk splits
into the left semicircle and the right semicircle split across the `0` angle. -/
theorem Complex.finiteAbelPlana_log_interiorCircleIntegral_eq_left_add_right
    (n : ℕ)
    (w : ℂ)
    (ρ : ℝ)
    (hfirst :
      IntervalIntegrable
        (fun θ : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        volume
        (0 : ℝ)
        (Real.pi / 2))
    (hsecond :
      IntervalIntegrable
        (fun θ : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        volume
        (Real.pi / 2)
        (3 * Real.pi / 2))
    (hthird :
      IntervalIntegrable
        (fun θ : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        volume
        (3 * Real.pi / 2)
        (2 * Real.pi)) :
    circleIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (n + 1 : ℂ)
        ρ =
      Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral n w ρ +
        Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ := by
  let F : ℝ → ℂ := fun θ : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hsplit_left :
      (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ) +
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2), F θ =
          ∫ θ : ℝ in (0 : ℝ)..(3 * Real.pi / 2), F θ :=
    intervalIntegral.integral_add_adjacent_intervals hfirst hsecond
  have hfirst_second :
      IntervalIntegrable F volume (0 : ℝ) (3 * Real.pi / 2) :=
    hfirst.trans hsecond
  have hsplit_right :
      (∫ θ : ℝ in (0 : ℝ)..(3 * Real.pi / 2), F θ) +
        ∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi), F θ =
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ :=
    intervalIntegral.integral_add_adjacent_intervals hfirst_second hthird
  have hcircle :
      circleIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (n + 1 : ℂ)
          ρ =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ := by
    unfold circleIntegral circleMap deriv_circleMap F
    congr 1
    ext θ
    exact Complex.circle_derivative_real_radius_commute ρ θ
  calc
    circleIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (n + 1 : ℂ)
        ρ =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), F θ := hcircle
    _ =
        (∫ θ : ℝ in (0 : ℝ)..(3 * Real.pi / 2), F θ) +
          ∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi), F θ := hsplit_right.symm
    _ =
        ((∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ) +
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2), F θ) +
            ∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi), F θ := by
      exact
        congrArg
          (fun z : ℂ =>
            z + ∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi), F θ)
          hsplit_left.symm
    _ =
        Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral n w ρ +
          Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ := by
      unfold Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral
        Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral F
      exact
        Complex.add_left_middle_right
          (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                (((n + 1 : ℕ) : ℂ) +
                  (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                (((n + 1 : ℕ) : ℂ) +
                  (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                (((n + 1 : ℕ) : ℂ) +
                  (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))

/-- Algebraic assembly of the two interior semicollars into the full punctured
rectangular collar boundary.

The three hypotheses are exactly the side-concatenation facts consumed by this
assembly step: lower horizontal concatenation, upper horizontal concatenation,
and the split of the full counterclockwise circle into its left and right
semicircular pieces.  The internal vertical diameter cancels algebraically. -/
theorem Complex.finiteAbelPlana_log_interiorPuncturedRectangularCollarBoundary_halfCollar_assembly
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hlower :
      Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ =
        Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ)
    (hupper :
      Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ =
        Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar n w T ρ)
    (hcircle :
      circleIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (n + 1 : ℂ)
          ρ =
        Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral n w ρ +
          Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ) :
    Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary
        w
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
        T
        (n + 1 : ℂ)
        ρ =
      Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary n w T ρ +
        Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary n w T ρ := by
  change
    Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
        Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
          Complex.I *
            Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
            circleIntegral
              (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
              (n + 1 : ℂ)
              ρ =
      Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary n w T ρ +
        Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary n w T ρ
  calc
    Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
        Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
          Complex.I *
            Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
            circleIntegral
              (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
              (n + 1 : ℂ)
              ρ =
      (Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ) -
        Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
          Complex.I *
            Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
            circleIntegral
              (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
              (n + 1 : ℂ)
              ρ := by
      exact congrArg
        (fun lower : ℂ =>
          lower - Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
            circleIntegral
              (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
              (n + 1 : ℂ)
              ρ)
        hlower
    _ =
      (Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ) -
        (Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar n w T ρ) +
          Complex.I *
            Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
            circleIntegral
              (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
              (n + 1 : ℂ)
              ρ := by
      exact congrArg
        (fun upper : ℂ =>
          (Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
              Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ) -
            upper +
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
            circleIntegral
              (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
              (n + 1 : ℂ)
              ρ)
        hupper
    _ =
      (Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ) -
        (Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar n w T ρ) +
          Complex.I *
            Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
            (Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral n w ρ +
              Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ) := by
      exact congrArg
        (fun circle : ℂ =>
          (Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
              Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ) -
            (Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar n w T ρ +
              Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar n w T ρ) +
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ -
            circle)
        hcircle
    _ =
      Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary n w T ρ +
        Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary n w T ρ := by
      unfold Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary
        Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary
      abel_nf

/-- The parametrized deleted circle around an interior integer lies in the
ambient finite punctured rectangle. -/
theorem Complex.finiteAbelPlana_log_interiorCirclePoint_mem_puncturedRectangle
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (θ : ℝ) :
    (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∈
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  let z : ℂ :=
    (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hρheight : ρ ≤ |T| := by
    have hρ_lt_absT : ρ < |T| := by
      have hhalf_lt_abs : |T| / 2 < |T| := by
        have hhalf_pos : 0 < |T| / 2 := lt_trans hρ hdeleted_geometry.2.1
        exact Real.half_lt_self_of_pos (by exact (half_pos.mp hhalf_pos))
      exact lt_trans hdeleted_geometry.2.1 hhalf_lt_abs
    exact le_of_lt hρ_lt_absT
  have hz_closed :
      z ∈ Metric.closedBall (n + 1 : ℂ) ρ := by
    have hz_eq : z = circleMap (n + 1 : ℂ) ρ θ := by
      exact Complex.finiteAbelPlana_interiorCircleParam_eq_circleMap n ρ θ
    exact hz_eq.symm ▸ circleMap_mem_closedBall (n + 1 : ℂ) hρnonneg θ
  have hz_rect :
      z.re ∈
          [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] ∧
        z.im ∈ [[-T, T]] :=
    Complex.finiteAbelPlanaLogInteriorCollarClosedDisk_subset_closedRectangle
      T n hρnonneg hρheight hz_closed
  have hz_not_central : z ∉ Metric.ball (n + 1 : ℂ) ρ := by
    have hz_eq : z = circleMap (n + 1 : ℂ) ρ θ := by
      exact Complex.finiteAbelPlana_interiorCircleParam_eq_circleMap n ρ θ
    exact hz_eq.symm ▸ circleMap_not_mem_ball (n + 1 : ℂ) ρ θ
  have hcollar_mem :
      z ∈
        Complex.finiteAbelPlanaLogPuncturedRectangularCollar
          (Complex.finiteAbelPlanaVerticalStripRight n ρ)
          (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
          T
          (n + 1 : ℂ)
          ρ :=
    Complex.mem_finiteAbelPlanaLogPuncturedRectangularCollar_iff.mpr
      ⟨hz_rect.1, hz_rect.2, hz_not_central⟩
  have hsubset :
      Complex.finiteAbelPlanaLogPuncturedRectangularCollar
          (Complex.finiteAbelPlanaVerticalStripRight n ρ)
          (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
          T
          (n + 1 : ℂ)
          ρ ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ :=
    Complex.finiteAbelPlanaLogInteriorPuncturedRectangularCollar_subset_puncturedRectangle
      T n hn hρnonneg hdeleted_geometry.1
  exact hsubset hcollar_mem

/-- Interval-integrability of the three angular pieces used to split the
interior deleted-circle contour into the left semicircle and the split right
semicircle. -/
theorem Complex.finiteAbelPlana_log_interiorCircleIntegral_split_intervalIntegrable
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    let F : ℝ → ℂ := fun θ : ℝ =>
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    IntervalIntegrable F volume (0 : ℝ) (Real.pi / 2) ∧
      IntervalIntegrable F volume (Real.pi / 2) (3 * Real.pi / 2) ∧
        IntervalIntegrable F volume (3 * Real.pi / 2) (2 * Real.pi) := by
  let F : ℝ → ℂ := fun θ : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hparam_cont :
      Continuous
        (fun θ : ℝ =>
          (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
    exact
      continuous_const.add
        (continuous_const.mul
          (Complex.continuous_exp.comp
            (continuous_const.mul continuous_ofReal)))
  have hderiv_cont :
      Continuous
        (fun θ : ℝ =>
          Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    exact
      (continuous_const.mul continuous_const).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul continuous_ofReal))
  have hinterval :
      ∀ a b : ℝ, IntervalIntegrable F volume a b := by
    intro a b
    have hparam_contOn :
        ContinuousOn
          (fun θ : ℝ =>
            (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          [[a, b]] :=
      hparam_cont.continuousOn
    have hpath :
        ∀ θ ∈ [[a, b]],
          (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∈
            Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
      intro θ _hθ
      exact
        Complex.finiteAbelPlana_log_interiorCirclePoint_mem_puncturedRectangle
          (w := w) n hn hρ hdeleted_geometry θ
    have hintegrand_cont :
        ContinuousOn
          (fun θ : ℝ =>
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          [[a, b]] :=
      hcont.comp_continuousOn hparam_contOn hpath
    have hfactor_cont :
        ContinuousOn
          (fun θ : ℝ =>
            Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          [[a, b]] :=
      hderiv_cont.continuousOn
    have hF_cont :
        ContinuousOn F [[a, b]] := by
      exact hintegrand_cont.mul hfactor_cont
    exact hF_cont.intervalIntegrable
  exact ⟨hinterval (0 : ℝ) (Real.pi / 2),
    hinterval (Real.pi / 2) (3 * Real.pi / 2),
    hinterval (3 * Real.pi / 2) (2 * Real.pi)⟩

/-- The lower and upper horizontal interior collar integrals split at the
vertical diameter through the deleted integer.

This is the interval-integrability bookkeeping needed before the actual
semicollar Cauchy-Goursat assembly: the lower and upper horizontal edges of the
interior punctured collar are each the concatenation of their left and right
semicollar pieces. -/
theorem Complex.finiteAbelPlana_log_interiorHorizontalCollar_splits_of_deletedGeometry
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ =
        Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ ∧
      Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ =
        Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar n w T ρ := by
  let i : ℕ := 2 * (n + 1)
  have hi : i < 2 * N + 3 := by
    have hnlt : n < N := Finset.mem_range.mp hn
    exact
      Nat.finiteAbelPlana_two_mul_succ_lt_two_mul_add_three_of_lt
        hnlt
  have hseg :
      (∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
        ((x : ℂ) + Complex.I * (T : ℂ)) ∈
          Complex.finiteAbelPlanaPuncturedRectangle N T ρ) ∧
      (∀ x ∈ [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]],
        ((x : ℂ) - Complex.I * (T : ℂ)) ∈
          Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :=
    Complex.finiteAbelPlana_horizontalSubdivision_segment_subset_puncturedRectangle
      hρ hdeleted_geometry hi
  have hend_left :
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i =
        Complex.finiteAbelPlanaVerticalStripRight n ρ := by
    calc
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i =
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1)) := rfl
      _ = Complex.finiteAbelPlanaVerticalStripRight n ρ :=
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_left
            N n ρ hn
  have hend_right :
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1) =
        Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ := by
    calc
      Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1) =
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (2 * (n + 1) + 1) := rfl
      _ = Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ :=
          Complex.finiteAbelPlana_horizontalSubdivisionEndpoint_interior_right
            N n ρ hn
  have hleft_sub :
      [[Complex.finiteAbelPlanaVerticalStripRight n ρ, ((n + 1 : ℕ) : ℝ)]] ⊆
        [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] := by
    intro x hx
    have hρnonneg : 0 ≤ ρ := le_of_lt hρ
    have hmem :
        x ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
          Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] :=
      Real.interior_left_half_subset_full_uIcc n hρnonneg hx
    have htarget :
        [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] =
        [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
          Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] :=
      congrArg₂ Set.uIcc hend_left hend_right
    exact htarget.symm ▸ hmem
  have hright_sub :
      [[((n + 1 : ℕ) : ℝ), Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] ⊆
        [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] := by
    intro x hx
    have hρnonneg : 0 ≤ ρ := le_of_lt hρ
    have hmem :
        x ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
          Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] :=
      Real.interior_right_half_subset_full_uIcc n hρnonneg hx
    have htarget :
        [[Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ i,
          Complex.finiteAbelPlanaHorizontalSubdivisionEndpoint N ρ (i + 1)]] =
        [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
          Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] :=
      congrArg₂ Set.uIcc hend_left hend_right
    exact htarget.symm ▸ hmem
  have lower_left_int :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) - Complex.I * (T : ℂ)))
        volume
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (((n + 1 : ℕ) : ℝ)) := by
    have hparam :
        ContinuousOn (fun x : ℝ => ((x : ℂ) - Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            ((n + 1 : ℕ) : ℝ)]] :=
      (Complex.continuous_ofReal.sub continuous_const).continuousOn
    have hmem :
        ∀ x ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            ((n + 1 : ℕ) : ℝ)]],
          ((x : ℂ) - Complex.I * (T : ℂ)) ∈
            Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
      intro x hx
      exact hseg.2 x (hleft_sub hx)
    exact (hcont.comp_continuousOn hparam hmem).intervalIntegrable
  have lower_right_int :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) - Complex.I * (T : ℂ)))
        volume
        (((n + 1 : ℕ) : ℝ))
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ) := by
    have hparam :
        ContinuousOn (fun x : ℝ => ((x : ℂ) - Complex.I * (T : ℂ)))
          [[((n + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] :=
      (Complex.continuous_ofReal.sub continuous_const).continuousOn
    have hmem :
        ∀ x ∈ [[((n + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]],
          ((x : ℂ) - Complex.I * (T : ℂ)) ∈
            Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
      intro x hx
      exact hseg.2 x (hright_sub hx)
    exact (hcont.comp_continuousOn hparam hmem).intervalIntegrable
  have upper_left_int :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + Complex.I * (T : ℂ)))
        volume
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (((n + 1 : ℕ) : ℝ)) := by
    have hparam :
        ContinuousOn (fun x : ℝ => ((x : ℂ) + Complex.I * (T : ℂ)))
          [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            ((n + 1 : ℕ) : ℝ)]] :=
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have hmem :
        ∀ x ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            ((n + 1 : ℕ) : ℝ)]],
          ((x : ℂ) + Complex.I * (T : ℂ)) ∈
            Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
      intro x hx
      exact hseg.1 x (hleft_sub hx)
    exact (hcont.comp_continuousOn hparam hmem).intervalIntegrable
  have upper_right_int :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((x : ℂ) + Complex.I * (T : ℂ)))
        volume
        (((n + 1 : ℕ) : ℝ))
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ) := by
    have hparam :
        ContinuousOn (fun x : ℝ => ((x : ℂ) + Complex.I * (T : ℂ)))
          [[((n + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] :=
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have hmem :
        ∀ x ∈ [[((n + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]],
          ((x : ℂ) + Complex.I * (T : ℂ)) ∈
            Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
      intro x hx
      exact hseg.1 x (hright_sub hx)
    exact (hcont.comp_continuousOn hparam hmem).intervalIntegrable
  exact
    ⟨Complex.finiteAbelPlana_log_interiorLowerCollar_eq_left_add_right
        n w T ρ lower_left_int lower_right_int,
      Complex.finiteAbelPlana_log_interiorUpperCollar_eq_left_add_right
        n w T ρ upper_left_int upper_right_int⟩

/-- Cauchy-Goursat on the left interior semicollar.

The left interior semicollar is the part of the punctured rectangular collar to
the left of the deleted integer center.  Its boundary consists of the lower and
upper horizontal semicollar pieces, the central vertical diameter, the left
safe strip side, and the counterclockwise left semicircle with negative
orientation. -/
theorem Complex.finiteAbelPlana_log_interiorLeftSemicollarBoundary_eq_zero_of_deletedGeometry
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary n w T ρ = 0 := by
  let c : ℂ := (n + 1 : ℂ)
  have hρ_absT : ρ < |T| := by
    have hhalf_lt_abs : |T| / 2 < |T| := by
      have hhalf_pos : 0 < |T| / 2 := lt_trans hρ hdeleted_geometry.2.1
      exact Real.half_lt_self_of_pos (by exact half_pos.mp hhalf_pos)
    exact lt_trans hdeleted_geometry.2.1 hhalf_lt_abs
  have hdomain_subset :
      Complex.leftHalfRectangleDeletedDiskDomain c T ρ ρ ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
    intro z hz
    have hzrect :
        z.re ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] ∧
          z.im ∈ [[-T, T]] ∧
            z ∉ Metric.ball (n + 1 : ℂ) ρ := by
      have hzmodel :
          (z.re ∈ [[((n + 1 : ℕ) : ℝ) - ρ, ((n + 1 : ℕ) : ℝ)]] ∧
            z.im ∈ [[-T, T]]) ∧
            z ∉ Metric.ball (n + 1 : ℂ) ρ :=
        (Complex.mem_leftHalfRectangleDeletedDiskDomain_interiorInteger_iff
          n T ρ z).mp hz
      have hzre_left :
          z.re ∈ [[((n + 1 : ℕ) : ℝ) - ρ, ((n + 1 : ℕ) : ℝ)]] := by
        exact hzmodel.1.1
      have hzim : z.im ∈ [[-T, T]] := by
        exact hzmodel.1.2
      have hnot : z ∉ Metric.ball (n + 1 : ℂ) ρ := by
        exact hzmodel.2
      have hρnonneg : 0 ≤ ρ := le_of_lt hρ
      have hzre_full :
          z.re ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] := by
        exact Real.interior_left_half_subset_full_uIcc n hρnonneg hzre_left
      exact ⟨hzre_full, hzim, hnot⟩
    have hcollar :
        z ∈
          Complex.finiteAbelPlanaLogPuncturedRectangularCollar
            (Complex.finiteAbelPlanaVerticalStripRight n ρ)
            (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
            T
            (n + 1 : ℂ)
            ρ :=
      Complex.mem_finiteAbelPlanaLogPuncturedRectangularCollar_iff.mpr hzrect
    exact
      (Complex.finiteAbelPlanaLogInteriorPuncturedRectangularCollar_subset_puncturedRectangle
        T n hn hρ.le hdeleted_geometry.1) hcollar
  have hcont_model :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.leftHalfRectangleDeletedDiskDomain c T ρ ρ) :=
    hcont.mono hdomain_subset
  have hdiff_model :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.leftHalfRectangleDeletedDiskDomain c T ρ ρ) :=
    hdiff.mono hdomain_subset
  have hlocal :
      -(∫ x : ℝ in (c.re - ρ)..c.re,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
          (∫ x : ℝ in (c.re - ρ)..c.re,
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                Complex.finiteAbelPlanaLogRectangleIntegrand w
                  (((c.re - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0 :=
    Complex.leftHalfRectangleDeletedDiskBoundary_eq_zero
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      c T ρ le_rfl hρ hρ_absT hcont_model hdiff_model
  unfold Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary
    Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar
    Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar
    Complex.finiteAbelPlanaLogInteriorCollarVerticalDiameter
    Complex.finiteAbelPlanaLogVerticalStripRightSide
    Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral
    Complex.finiteAbelPlanaVerticalStripRight at hlocal ⊢
  unfold c at hlocal ⊢
  abel_nf at hlocal ⊢
  exact hlocal

/-- The split right semicircle around an interior deleted integer is the same
right-half arc as the interval `[-π / 2, π / 2]`.

This is only a periodic reparametrization of the circle map; the split form is
used because `circleIntegral` is parametrized on `[0, 2π]`, while the local
right half-rectangle theorem uses the connected right-half interval. -/
theorem Complex.finiteAbelPlana_log_interiorCircleArcIntegrand_periodic
    (n : ℕ)
    (w : ℂ)
    (ρ : ℝ) :
    Function.Periodic
      (fun θ : ℝ =>
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (2 * Real.pi) := by
  intro θ
  have hexp :
      Complex.exp (Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (θ : ℂ)) := by
    calc
      Complex.exp (Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ)) =
          Complex.exp (Complex.I * (θ : ℂ) + (2 * Real.pi * Complex.I)) := by
        exact congrArg Complex.exp (Complex.I_mul_ofReal_add_two_pi θ)
      _ =
          Complex.exp (Complex.I * (θ : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I) :=
        Complex.exp_add (Complex.I * (θ : ℂ)) (2 * Real.pi * Complex.I)
      _ = Complex.exp (Complex.I * (θ : ℂ)) * 1 := by
        exact congrArg
          (fun z : ℂ => Complex.exp (Complex.I * (θ : ℂ)) * z)
          Complex.exp_two_pi_mul_I
      _ = Complex.exp (Complex.I * (θ : ℂ)) :=
        mul_one (Complex.exp (Complex.I * (θ : ℂ)))
  exact congrArg₂ HMul.hMul
    (congrArg
      (fun z : ℂ =>
        Complex.finiteAbelPlanaLogRectangleIntegrand w
          (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * z))
      hexp)
    (congrArg
      (fun z : ℂ => Complex.I * (ρ : ℂ) * z)
      hexp)

theorem Complex.finiteAbelPlana_log_interiorRightSemicircleSplitIntegral_eq_rightHalfArc
    (n : ℕ)
    (w : ℂ)
    (ρ : ℝ)
    (hfirst :
      IntervalIntegrable
        (fun θ : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        volume
        (0 : ℝ)
        (Real.pi / 2))
    (hthird :
      IntervalIntegrable
        (fun θ : ℝ =>
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        volume
        (3 * Real.pi / 2)
        (2 * Real.pi)) :
    Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  let F : ℝ → ℂ := fun θ : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hperiodic : Function.Periodic F (2 * Real.pi) :=
    Complex.finiteAbelPlana_log_interiorCircleArcIntegrand_periodic n w ρ
  have hsplit :
      Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ =
        (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ) +
          ∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi), F θ := by
    rfl
  have htranslate :
      (∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi), F θ) =
        ∫ θ : ℝ in (-(Real.pi / 2))..(0 : ℝ), F θ := by
    have hcomp :
        (∫ θ : ℝ in (-(Real.pi / 2))..(0 : ℝ), F (θ + 2 * Real.pi)) =
          ∫ θ : ℝ in (-(Real.pi / 2) + 2 * Real.pi)..(0 + 2 * Real.pi), F θ :=
      intervalIntegral.integral_comp_add_right F (2 * Real.pi)
    have hperiodic_on :
        (fun θ : ℝ => F (θ + 2 * Real.pi)) = F := by
      funext θ
      exact hperiodic θ
    have hleft :
        (-(Real.pi / 2) + 2 * Real.pi) = 3 * Real.pi / 2 :=
      Real.neg_pi_div_two_add_two_pi_eq_three_pi_div_two
    have hright :
        (0 : ℝ) + 2 * Real.pi = 2 * Real.pi :=
      Real.zero_add_two_pi_eq_two_pi
    have hdomain_transport :
        (∫ θ : ℝ in (-(Real.pi / 2) + 2 * Real.pi)..(0 + 2 * Real.pi), F θ) =
          ∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi), F θ :=
      congrArg₂
        (fun a b : ℝ => ∫ θ : ℝ in a..b, F θ)
        hleft
        hright
    have hsource_transport :
        (∫ θ : ℝ in (-(Real.pi / 2))..(0 : ℝ), F (θ + 2 * Real.pi)) =
          ∫ θ : ℝ in (-(Real.pi / 2))..(0 : ℝ), F θ :=
      congrArg
        (fun G : ℝ → ℂ => ∫ θ : ℝ in (-(Real.pi / 2))..(0 : ℝ), G θ)
        hperiodic_on
    exact
      (Eq.trans
        (Eq.trans hsource_transport.symm hcomp)
        hdomain_transport).symm
  have hneg :
      IntervalIntegrable F volume (-(Real.pi / 2)) (0 : ℝ) := by
    have htranslated :
        IntervalIntegrable (fun θ : ℝ => F (θ + 2 * Real.pi)) volume
          (3 * Real.pi / 2 - 2 * Real.pi)
          (2 * Real.pi - 2 * Real.pi) :=
      hthird.comp_add_right (2 * Real.pi)
    have hperiodic_fun :
        (fun θ : ℝ => F (θ + 2 * Real.pi)) = F := by
      funext θ
      exact hperiodic θ
    have hfunction_transport :
        IntervalIntegrable F volume
          (3 * Real.pi / 2 - 2 * Real.pi)
          (2 * Real.pi - 2 * Real.pi) :=
      Eq.mp
        (congrArg
          (fun G : ℝ → ℂ =>
            IntervalIntegrable G volume
              (3 * Real.pi / 2 - 2 * Real.pi)
              (2 * Real.pi - 2 * Real.pi))
          hperiodic_fun)
        htranslated
    have hleft :
        3 * Real.pi / 2 - 2 * Real.pi = -(Real.pi / 2) :=
      Real.three_pi_div_two_sub_two_pi_eq_neg_pi_div_two
    have hright :
        2 * Real.pi - 2 * Real.pi = (0 : ℝ) :=
      Real.two_pi_sub_two_pi_eq_zero
    exact
      Eq.mp
        (congrArg₂
          (fun a b : ℝ => IntervalIntegrable F volume a b)
          hleft
          hright)
        hfunction_transport
  have hconcat :
      (∫ θ : ℝ in (-(Real.pi / 2))..(0 : ℝ), F θ) +
          ∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), F θ := by
    exact
      intervalIntegral.integral_add_adjacent_intervals
        hneg
        hfirst
  calc
    Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ =
        (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ) +
          ∫ θ : ℝ in (3 * Real.pi / 2)..(2 * Real.pi), F θ := hsplit
    _ =
        (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ) +
          ∫ θ : ℝ in (-(Real.pi / 2))..(0 : ℝ), F θ := by
      exact
        congrArg
          (fun z : ℂ => (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ) + z)
          htranslate
    _ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), F θ := by
      exact
        Eq.trans
          (add_comm
            (∫ θ : ℝ in (0 : ℝ)..(Real.pi / 2), F θ)
            (∫ θ : ℝ in (-(Real.pi / 2))..(0 : ℝ), F θ))
          hconcat
    _ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
      rfl

/-- Cauchy-Goursat on the right interior semicollar.

The right interior semicollar is the reflected part of the punctured
rectangular collar.  The central vertical diameter appears with the opposite
orientation, so it cancels against the left semicollar after assembly. -/
theorem Complex.finiteAbelPlana_log_interiorRightSemicollarBoundary_eq_zero_of_deletedGeometry
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary n w T ρ = 0 := by
  let c : ℂ := (n + 1 : ℂ)
  have hρ_absT : ρ < |T| := by
    have hhalf_lt_abs : |T| / 2 < |T| := by
      have hhalf_pos : 0 < |T| / 2 := lt_trans hρ hdeleted_geometry.2.1
      exact Real.half_lt_self_of_pos (by exact half_pos.mp hhalf_pos)
    exact lt_trans hdeleted_geometry.2.1 hhalf_lt_abs
  have hdomain_subset :
      Complex.rightHalfRectangleDeletedDiskDomain c T ρ ρ ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
    intro z hz
    have hzrect :
        z.re ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] ∧
          z.im ∈ [[-T, T]] ∧
            z ∉ Metric.ball (n + 1 : ℂ) ρ := by
      have hzmodel :
          (z.re ∈ [[((n + 1 : ℕ) : ℝ), ((n + 1 : ℕ) : ℝ) + ρ]] ∧
            z.im ∈ [[-T, T]]) ∧
            z ∉ Metric.ball (n + 1 : ℂ) ρ :=
        (Complex.mem_rightHalfRectangleDeletedDiskDomain_interiorInteger_iff
          n T ρ z).mp hz
      have hzre_right :
          z.re ∈ [[((n + 1 : ℕ) : ℝ), ((n + 1 : ℕ) : ℝ) + ρ]] := by
        exact hzmodel.1.1
      have hzim : z.im ∈ [[-T, T]] := by
        exact hzmodel.1.2
      have hnot : z ∉ Metric.ball (n + 1 : ℂ) ρ := by
        exact hzmodel.2
      have hρnonneg : 0 ≤ ρ := le_of_lt hρ
      have hzre_full :
          z.re ∈ [[Complex.finiteAbelPlanaVerticalStripRight n ρ,
            Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ]] := by
        exact Real.interior_right_half_subset_full_uIcc n hρnonneg hzre_right
      exact ⟨hzre_full, hzim, hnot⟩
    have hcollar :
        z ∈
          Complex.finiteAbelPlanaLogPuncturedRectangularCollar
            (Complex.finiteAbelPlanaVerticalStripRight n ρ)
            (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
            T
            (n + 1 : ℂ)
            ρ :=
      Complex.mem_finiteAbelPlanaLogPuncturedRectangularCollar_iff.mpr hzrect
    exact
      (Complex.finiteAbelPlanaLogInteriorPuncturedRectangularCollar_subset_puncturedRectangle
        T n hn hρ.le hdeleted_geometry.1) hcollar
  have hcont_model :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.rightHalfRectangleDeletedDiskDomain c T ρ ρ) :=
    hcont.mono hdomain_subset
  have hdiff_model :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.rightHalfRectangleDeletedDiskDomain c T ρ ρ) :=
    hdiff.mono hdomain_subset
  have hlocal :
      -(∫ x : ℝ in c.re..(c.re + ρ),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
          (∫ x : ℝ in c.re..(c.re + ρ),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
            Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                Complex.finiteAbelPlanaLogRectangleIntegrand w
                  (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0 :=
    Complex.rightHalfRectangleDeletedDiskBoundary_eq_zero
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      c T ρ le_rfl hρ hρ_absT hcont_model hdiff_model
  let F : ℝ → ℂ := fun θ : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hcircle_integrable :
      IntervalIntegrable F volume (0 : ℝ) (Real.pi / 2) ∧
        IntervalIntegrable F volume (Real.pi / 2) (3 * Real.pi / 2) ∧
          IntervalIntegrable F volume (3 * Real.pi / 2) (2 * Real.pi) :=
    Complex.finiteAbelPlana_log_interiorCircleIntegral_split_intervalIntegrable
      N T n hn hρ hdeleted_geometry hcont
  have harc :
      Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.finiteAbelPlana_log_interiorRightSemicircleSplitIntegral_eq_rightHalfArc
      n w ρ hcircle_integrable.1 hcircle_integrable.2.2
  unfold Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary
    Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar
    Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar
    Complex.finiteAbelPlanaLogVerticalStripLeftSide
    Complex.finiteAbelPlanaLogInteriorCollarVerticalDiameter
    Complex.finiteAbelPlanaVerticalStripLeft at hlocal ⊢
  unfold c at hlocal ⊢
  exact harc ▸ by
    abel_nf at hlocal ⊢
    exact hlocal

/-- Cauchy-Goursat for the standard interior Abel-Plana punctured rectangular
collar, assembled from the two semicollar Cauchy-Goursat identities. -/
theorem Complex.finiteAbelPlana_log_interiorPuncturedRectangularCollarBoundary_eq_zero_of_semicollarCauchy
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hlower :
      Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ =
        Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ)
    (hupper :
      Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ =
        Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar n w T ρ +
          Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar n w T ρ)
    (hcircle :
      circleIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (n + 1 : ℂ)
          ρ =
        Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral n w ρ +
          Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary
        w
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
        T
        (n + 1 : ℂ)
        ρ = 0 := by
  have hleft :
      Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary n w T ρ = 0 :=
    Complex.finiteAbelPlana_log_interiorLeftSemicollarBoundary_eq_zero_of_deletedGeometry
      N T n hn hρ hdeleted_geometry hcont hdiff
  have hright :
      Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary n w T ρ = 0 :=
    Complex.finiteAbelPlana_log_interiorRightSemicollarBoundary_eq_zero_of_deletedGeometry
      N T n hn hρ hdeleted_geometry hcont hdiff
  have hassembly :
      Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary
          w
          (Complex.finiteAbelPlanaVerticalStripRight n ρ)
          (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
          T
          (n + 1 : ℂ)
          ρ =
        Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary n w T ρ +
          Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary n w T ρ :=
    Complex.finiteAbelPlana_log_interiorPuncturedRectangularCollarBoundary_halfCollar_assembly
      n w T ρ hlower hupper hcircle
  calc
    Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary
        w
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
        T
        (n + 1 : ℂ)
        ρ =
      Complex.finiteAbelPlanaLogInteriorLeftSemicollarBoundary n w T ρ +
        Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary n w T ρ :=
      hassembly
    _ = 0 + Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary n w T ρ := by
      exact congrArg
        (fun z : ℂ => z + Complex.finiteAbelPlanaLogInteriorRightSemicollarBoundary n w T ρ)
        hleft
    _ = 0 + 0 := by
      exact congrArg
        (fun z : ℂ => 0 + z)
        hright
    _ = 0 := zero_add (0 : ℂ)

/-- Cauchy-Goursat for the standard interior Abel-Plana punctured rectangular
collar, specialized to the collar around the interior integer `n + 1`. -/
theorem Complex.finiteAbelPlana_log_interiorPuncturedRectangularCollarBoundary_eq_zero_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary
        w
        (Complex.finiteAbelPlanaVerticalStripRight n ρ)
        (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
        T
        (n + 1 : ℂ)
        ρ = 0 := by
  have hsplits :
      Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ =
          Complex.finiteAbelPlanaLogInteriorLowerLeftSemicollar n w T ρ +
            Complex.finiteAbelPlanaLogInteriorLowerRightSemicollar n w T ρ ∧
        Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ =
          Complex.finiteAbelPlanaLogInteriorUpperLeftSemicollar n w T ρ +
            Complex.finiteAbelPlanaLogInteriorUpperRightSemicollar n w T ρ :=
    Complex.finiteAbelPlana_log_interiorHorizontalCollar_splits_of_deletedGeometry
      N T n hn hρ hdeleted_geometry hcont
  let F : ℝ → ℂ := fun θ : ℝ =>
    Complex.finiteAbelPlanaLogRectangleIntegrand w
        (((n + 1 : ℕ) : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hcircle_integrable :
      IntervalIntegrable F volume (0 : ℝ) (Real.pi / 2) ∧
        IntervalIntegrable F volume (Real.pi / 2) (3 * Real.pi / 2) ∧
          IntervalIntegrable F volume (3 * Real.pi / 2) (2 * Real.pi) :=
    Complex.finiteAbelPlana_log_interiorCircleIntegral_split_intervalIntegrable
      N T n hn hρ hdeleted_geometry hcont
  have hcircle :
      circleIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (n + 1 : ℂ)
          ρ =
        Complex.finiteAbelPlanaLogInteriorLeftSemicircleIntegral n w ρ +
          Complex.finiteAbelPlanaLogInteriorRightSemicircleSplitIntegral n w ρ :=
    Complex.finiteAbelPlana_log_interiorCircleIntegral_eq_left_add_right
      n w ρ
      hcircle_integrable.1
      hcircle_integrable.2.1
      hcircle_integrable.2.2
  exact
    Complex.finiteAbelPlana_log_interiorPuncturedRectangularCollarBoundary_eq_zero_of_semicollarCauchy
      N T n hn hρ hdeleted_geometry hsplits.1 hsplits.2 hcircle hcont hdiff

/-- Cauchy-Goursat on the punctured interior cap/collar subdomain around the
deleted disk centered at `n + 1`.

This is the genuine local analytic/topological input for the interior collar:
the logarithmic cotangent integrand is holomorphic on the collar after deleting
the small disk, the closed collar boundary is contained in the finite punctured
rectangle, and the boundary orientation is the standard positive outer boundary
minus the counterclockwise inner circle. -/
theorem Complex.finiteAbelPlana_log_interiorCapCollarPuncturedBoundary_eq_zero_of_deletedGeometry
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary n w T ρ = 0 := by
  calc
    Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary n w T ρ =
        Complex.finiteAbelPlanaLogPuncturedRectangularCollarBoundary
          w
          (Complex.finiteAbelPlanaVerticalStripRight n ρ)
          (Complex.finiteAbelPlanaVerticalStripLeft (n + 1) ρ)
          T
          (n + 1 : ℂ)
          ρ := by
      exact
        Complex.finiteAbelPlana_log_interiorCapCollarPuncturedBoundary_eq_puncturedRectangularCollarBoundary
          n w T ρ
    _ = 0 := by
      exact
        Complex.finiteAbelPlana_log_interiorPuncturedRectangularCollarBoundary_eq_zero_owner
          N T n hn hρ hdeleted_geometry hcont hdiff

/-- Solving the punctured-collar Cauchy equation for the interior deleted-circle
integral gives the unnormalized local collar balance. -/
theorem Complex.finiteAbelPlana_log_interiorCapCollar_unnormalizedCauchy_balance_of_puncturedBoundary_zero
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary n w T ρ = 0) :
    Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
        Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
          Complex.I *
            Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ =
      circleIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (n + 1 : ℂ)
        ρ := by
  unfold Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary at hboundary
  exact sub_eq_zero.mp hboundary

/-- The interior punctured-collar boundary vanishes exactly when the straight
collar boundary equals the counterclockwise deleted-circle integral. -/
theorem Complex.finiteAbelPlana_log_interiorCapCollarPuncturedBoundary_eq_zero_iff_balance
    (n : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary n w T ρ = 0 ↔
      Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
          Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I *
                Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ =
        circleIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (n + 1 : ℂ)
          ρ := by
  constructor
  · intro hboundary
    exact
      Complex.finiteAbelPlana_log_interiorCapCollar_unnormalizedCauchy_balance_of_puncturedBoundary_zero
        n w T ρ hboundary
  · intro hbalance
    unfold Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary
    exact sub_eq_zero.mpr hbalance

/-- Unnormalized local Cauchy-Goursat balance for the interior collar around
the deleted disk centered at `n + 1`.

The contour is the interior cap/collar subdomain: the lower horizontal collar,
the adjacent right safe-strip vertical edge, the upper horizontal collar with
opposite orientation, the adjacent left safe-strip vertical edge with opposite
orientation, and the full deleted circle around the integer pole.  Cauchy's
theorem on that punctured collar says the sum of these oriented pieces is zero;
equivalently, the straight collar boundary equals the full small-circle integral
with the displayed orientation. -/
theorem Complex.finiteAbelPlana_log_interiorCapCollar_unnormalizedCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
        Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
          Complex.I *
            Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ =
	    circleIntegral
	      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
	      (n + 1 : ℂ)
	      ρ := by
  have hboundary :
      Complex.finiteAbelPlanaLogInteriorCapCollarPuncturedBoundary n w T ρ = 0 :=
    Complex.finiteAbelPlana_log_interiorCapCollarPuncturedBoundary_eq_zero_of_deletedGeometry
      N T n hn hρ hdeleted_geometry hcont hdiff
  exact
    Complex.finiteAbelPlana_log_interiorCapCollar_unnormalizedCauchy_balance_of_puncturedBoundary_zero
      n w T ρ hboundary

/-- One interior collar around the deleted disk centered at `n + 1` contributes
exactly that deleted small circle after the adjacent safe-strip straight edges
are cancelled.

This is the normalized form of the local Cauchy-Goursat theorem for an interior
deleted integer pole in the finite Abel-Plana rectangle.  The analytic content
is isolated in
`finiteAbelPlana_log_interiorCapCollar_unnormalizedCauchy_balance`; this wrapper
only applies the residue-theorem normalization factor. -/
theorem Complex.finiteAbelPlana_log_interiorCapCollarCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (n : ℕ)
    (hn : n ∈ Finset.range N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ m ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w m)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogInteriorCapCollarBoundary n w T ρ =
      Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ := by
  have hlocal :
      Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
          Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I *
                Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ =
        circleIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (n + 1 : ℂ)
          ρ :=
    Complex.finiteAbelPlana_log_interiorCapCollar_unnormalizedCauchy_balance
      N T n hn hρ hdeleted_geometry hcont hdiff
  change
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogInteriorLowerCollar n w T ρ -
          Complex.finiteAbelPlanaLogInteriorUpperCollar n w T ρ +
            Complex.I *
              Complex.finiteAbelPlanaLogVerticalStripLeftSide (n + 1) w T ρ -
              Complex.I *
                Complex.finiteAbelPlanaLogVerticalStripRightSide n w T ρ) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          (n + 1 : ℂ)
          ρ
  exact
    congrArg
      (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
      hlocal

/-- The closed `k`-th safe vertical strip lies in the punctured rectangle under
the deleted-disk geometry hypotheses. -/
theorem Complex.finiteAbelPlana_log_verticalStrip_closed_subset_puncturedRectangle_of_deletedGeometry
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (k : ℕ)
    (hk : k ∈ Complex.finiteAbelPlanaVerticalStripIndexSet N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    ([[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).re,
        (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).re]] ×ℂ
      [[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).im,
        (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).im]]) ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hρquarter : ρ < (1 : ℝ) / 4 := hdeleted_geometry.1
  have hstrip_subset :
      Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip N T ρ k ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ :=
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_subset_puncturedRectangle
      hk hρnonneg hρquarter
  intro z hz
  have hleft_le_right :
      Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k ≤
        Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k :=
    Complex.finiteAbelPlanaLogFiniteHoleVerticalStrip_left_le_right hρquarter k
  have hzdata := Complex.mem_reProdIm.mp hz
  have hzre :
      z.re ∈ Set.Icc
        (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k)
        (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k) := by
    have hset :
        [[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).re,
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).re]] =
          Set.Icc
            (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft ρ k)
            (Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight ρ k) := by
      unfold Complex.finiteAbelPlanaVerticalStripLowerLeftCorner
      unfold Complex.finiteAbelPlanaVerticalStripUpperRightCorner
      unfold Complex.finiteAbelPlanaLogFiniteHoleVerticalStripLeft
      unfold Complex.finiteAbelPlanaLogFiniteHoleVerticalStripRight
      exact Set.uIcc_of_le hleft_le_right
    exact Eq.mp (congrArg (fun S : Set ℝ => z.re ∈ S) hset) hzdata.1
  have hzim : z.im ∈ [[-T, T]] := by
    have hset :
        [[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).im,
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).im]] =
          [[-T, T]] := by
      unfold Complex.finiteAbelPlanaVerticalStripLowerLeftCorner
      unfold Complex.finiteAbelPlanaVerticalStripUpperRightCorner
      rfl
    exact Eq.mp (congrArg (fun S : Set ℝ => z.im ∈ S) hset) hzdata.2
  exact hstrip_subset (Complex.mem_reProdIm.mpr ⟨hzre, hzim⟩)

/-- The open interior of the `k`-th safe vertical strip lies in the punctured
rectangle under the deleted-disk geometry hypotheses. -/
theorem Complex.finiteAbelPlana_log_verticalStrip_open_subset_puncturedRectangle_of_deletedGeometry
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (k : ℕ)
    (hk : k ∈ Complex.finiteAbelPlanaVerticalStripIndexSet N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    (Set.Ioo
        (min
          (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).re
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).re)
        (max
          (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).re
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).re) ×ℂ
      Set.Ioo
        (min
          (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).im
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).im)
        (max
          (Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).im
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).im)) ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  have hclosed :
      ([[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).re,
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).re]] ×ℂ
        [[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).im,
          (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).im]]) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ :=
    Complex.finiteAbelPlana_log_verticalStrip_closed_subset_puncturedRectangle_of_deletedGeometry
      N T k hk hρ hdeleted_geometry
  intro z hz
  have hzdata := Complex.mem_reProdIm.mp hz
  have hzre :
      z.re ∈ [[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).re,
        (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).re]] :=
    Set.Ioo_subset_uIcc_self hzdata.1
  have hzim :
      z.im ∈ [[(Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ).im,
        (Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ).im]] :=
    Set.Ioo_subset_uIcc_self hzdata.2
  exact hclosed (Complex.mem_reProdIm.mpr ⟨hzre, hzim⟩)

/-- One ordinary safe vertical strip has zero normalized boundary contribution
by Cauchy-Goursat. -/
theorem Complex.finiteAbelPlana_log_verticalStripBoundaryIntegral_eq_zero_of_deletedGeometry
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (k : ℕ)
    (hk : k ∈ Complex.finiteAbelPlanaVerticalStripIndexSet N)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral k w T ρ = 0 := by
  let z₀ : ℂ := Complex.finiteAbelPlanaVerticalStripLowerLeftCorner k T ρ
  let z₁ : ℂ := Complex.finiteAbelPlanaVerticalStripUpperRightCorner k T ρ
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
    exact
      Complex.finiteAbelPlana_log_verticalStrip_closed_subset_puncturedRectangle_of_deletedGeometry
        N T k hk hρ hdeleted_geometry
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
        Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
    exact
      Complex.finiteAbelPlana_log_verticalStrip_open_subset_puncturedRectangle_of_deletedGeometry
        N T k hk hρ hdeleted_geometry
  have hrect :
      Complex.finiteAbelPlanaLogRectangleBoundaryIntegral w z₀ z₁ = 0 := by
    exact
      Complex.finiteAbelPlana_log_rectangleBoundaryIntegral_eq_zero_of_subset_puncturedRectangle_of_holomorphic
        N T z₀ z₁ hcont hdiff hclosed hopen
  calc
    Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral k w T ρ =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          Complex.finiteAbelPlanaLogRectangleBoundaryIntegral w z₀ z₁ := by
      unfold z₀ z₁ Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral
        Complex.finiteAbelPlanaLogRectangleBoundaryIntegral
        Complex.finiteAbelPlanaVerticalStripLowerLeftCorner
        Complex.finiteAbelPlanaVerticalStripUpperRightCorner
        Complex.finiteAbelPlanaLogVerticalStripLowerSide
        Complex.finiteAbelPlanaLogVerticalStripUpperSide
        Complex.finiteAbelPlanaLogVerticalStripLeftSide
        Complex.finiteAbelPlanaLogVerticalStripRightSide
        Complex.finiteAbelPlanaVerticalStripLeft
        Complex.finiteAbelPlanaVerticalStripRight
      abel_nf
    _ = 0 := by
      calc
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            Complex.finiteAbelPlanaLogRectangleBoundaryIntegral w z₀ z₁ =
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * 0 := by
          exact congrArg
            (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
            hrect
        _ = 0 := mul_zero (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)

/-- Each ordinary vertical safe strip in the finite Abel-Plana subdivision has
zero normalized boundary contribution.

This is the Cauchy-Goursat theorem on the pole-free rectangular strips between
neighboring deleted integer disks.  The geometric work is to show every closed
strip and every open strip interior lies in the punctured rectangle. -/
theorem Complex.finiteAbelPlana_log_verticalStripBoundarySum_eq_zero_of_deletedGeometry
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ = 0 := by
  calc
    Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
        ∑ k in Complex.finiteAbelPlanaVerticalStripIndexSet N,
          Complex.finiteAbelPlanaLogVerticalStripBoundaryIntegral k w T ρ :=
      Complex.finiteAbelPlana_log_verticalStripBoundarySum_unfold N w T ρ
    _ = 0 :=
      Finset.sum_eq_zero
        (fun k hk =>
          Complex.finiteAbelPlana_log_verticalStripBoundaryIntegral_eq_zero_of_deletedGeometry
            N T k hk hρ hdeleted_geometry hcont hdiff)

/-- The endpoint and interior cap/collar boundaries alone assemble to the
finite deleted-boundary contribution once the local collar Cauchy identities
are known. -/
theorem Complex.finiteAbelPlana_log_capCollarCauchy_balances_sum_to_deletedBoundary_without_strips
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ =
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ)
    (hright :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ =
        Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
    (hinterior :
      ∀ n ∈ Finset.range N,
        Complex.finiteAbelPlanaLogInteriorCapCollarBoundary n w T ρ =
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  have hinterior_sum :
      (∑ n in Finset.range N,
          Complex.finiteAbelPlanaLogInteriorCapCollarBoundary n w T ρ) =
        ∑ n in Finset.range N,
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ := by
    exact Finset.sum_congr rfl hinterior
  calc
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
        Complex.finiteAbelPlanaLogEndpointCapCollarBoundaryContribution N w T ρ +
          Complex.finiteAbelPlanaLogInteriorCapCollarBoundaryContribution N w T ρ := by
      exact
        Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_unfold
          N w T ρ
    _ =
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ +
          Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ) +
          (∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogInteriorCapCollarBoundary n w T ρ) := by
      exact congrArg₂ HAdd.hAdd
        (Complex.finiteAbelPlana_log_endpointCapCollarBoundaryContribution_unfold
          N w T ρ)
        (Complex.finiteAbelPlana_log_interiorCapCollarBoundaryContribution_unfold
          N w T ρ)
    _ =
        (Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
          Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ) +
          (∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ) := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd hleft hright)
        hinterior_sum
    _ =
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
          Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ := by
      exact (add_assoc
        (Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ)
        (Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
        (∑ n in Finset.range N,
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ)).symm
    _ =
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        (Complex.finiteAbelPlana_log_deletedBoundaryContribution_decomposition
          N w ρ).symm

/-- Summing the endpoint and interior collar Cauchy balances cancels the
auxiliary adjacent-strip terms and leaves the deleted-boundary contribution.

This is the finite algebraic assembly step after the local Cauchy-Goursat
calculations have been proved. -/
theorem Complex.finiteAbelPlana_log_capCollarCauchy_balances_sum_to_deletedBoundary
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ =
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ)
    (hright :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ =
        Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
    (hinterior :
      ∀ n ∈ Finset.range N,
        Complex.finiteAbelPlanaLogInteriorCapCollarBoundary n w T ρ =
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ)
    (hstrips :
      Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ = 0) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ +
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
      Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  have hcap :
      Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
    exact
      Complex.finiteAbelPlana_log_capCollarCauchy_balances_sum_to_deletedBoundary_without_strips
        N T hleft hright hinterior
  calc
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ +
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
      Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ + 0 := by
        exact congrArg₂ HAdd.hAdd hcap hstrips
    _ = Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
        exact add_zero
          (Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)

/-- Concrete cap/collar Cauchy balance for the finite-hole subdivision.

This is the direct planar Cauchy-Goursat statement, before solving for the
cap/collar contribution.  Apply Cauchy-Goursat to the two endpoint
cap/collar subdomains and to the `N` interior cap/collar subdomains.  The
straight collar edges cancel the adjacent finite vertical-strip boundary
edges, and the only surviving curved pieces are exactly the two endpoint
indentations and the `N` interior deleted circles. -/
theorem Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_add_verticalStripBoundarySum_eq_deletedBoundaryContribution_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ +
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
      Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
  have hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ =
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ := by
    exact
      Complex.finiteAbelPlana_log_leftEndpointCapCollarCauchy_balance
        N T hT hρ hdeleted_geometry hcont hdiff
  have hright :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ =
        Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ := by
    exact
      Complex.finiteAbelPlana_log_rightEndpointCapCollarCauchy_balance
        N T hT hρ hdeleted_geometry hcont hdiff
  have hinterior :
      ∀ n ∈ Finset.range N,
        Complex.finiteAbelPlanaLogInteriorCapCollarBoundary n w T ρ =
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ := by
    intro n hn
    exact
      Complex.finiteAbelPlana_log_interiorCapCollarCauchy_balance
        N T n hn hρ hdeleted_geometry hcont hdiff
  have hstrips :
      Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ = 0 := by
    exact
      Complex.finiteAbelPlana_log_verticalStripBoundarySum_eq_zero_of_deletedGeometry
        N T hρ hdeleted_geometry hcont hdiff
  exact
    Complex.finiteAbelPlana_log_capCollarCauchy_balances_sum_to_deletedBoundary
      N T hleft hright hinterior hstrips

/-- Concrete cap/collar Cauchy accounting for the finite-hole subdivision.

This is the version whose left-hand side is the explicit sum of the two
endpoint collar rectangles and all interior collar rectangles.  The proof is
the ordinary finite planar argument: apply Cauchy-Goursat on each collar
subdomain, cancel all internal straight edges against the adjacent vertical
safe strips, and identify the remaining curved deleted-boundary arcs with the
principal-value deleted-boundary contribution. -/
theorem Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_deletedBoundaryContribution_sub_verticalStripBoundarySum_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ -
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
  have hbalance :
      Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ +
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ =
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
    exact
      Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_add_verticalStripBoundarySum_eq_deletedBoundaryContribution_owner
        N T hT hρ hdeleted_geometry hcont hdiff
  calc
    Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ =
        (Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ +
            Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ) -
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
      exact Eq.symm
        (add_sub_cancel_right
          (Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ)
          (Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ))
    _ =
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ -
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
      exact congrArg
        (fun z : ℂ =>
          z - Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ)
        hbalance

/-- Cap/collar Cauchy accounting for the finite-hole subdivision.

The vertical safe strips omit exactly the collar regions around the endpoint
semicircles and interior deleted disks.  Summing Cauchy-Goursat over those
collar pieces cancels their straight internal edges and leaves precisely the
deleted-boundary contribution, with the opposite vertical-strip remainder.
This is the remaining planar decomposition theorem; after it is proved, the
finite-hole subdivision boundary vanishes by algebra. -/
theorem Complex.finiteAbelPlana_log_capCollarBoundaryContribution_eq_deletedBoundaryContribution_sub_verticalStripBoundarySum_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ =
      Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ -
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
  calc
    Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ =
        Complex.finiteAbelPlanaLogConcreteCapCollarBoundaryContribution N w T ρ := by
      exact
        (Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_capCollarBoundaryContribution
          N T hT hρ hdeleted_geometry hcont).symm
    _ =
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ -
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
      exact
        Complex.finiteAbelPlana_log_concreteCapCollarBoundaryContribution_eq_deletedBoundaryContribution_sub_verticalStripBoundarySum_owner
          N T hT hρ hdeleted_geometry hcont hdiff

/-- The zero-side gluing theorem for the full finite-hole subdivision.

The vertical safe strips alone are not the whole finite-hole subdivision:
between adjacent strips sit the cap/collar pieces around the deleted endpoint
semicircles and interior circles.  After adding those ordinary Cauchy pieces,
all straight internal edges cancel, and the only surviving contribution is the
deleted-boundary contribution. -/
theorem Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_zero_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ = 0 := by
  have hcap :
      Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ =
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ -
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ := by
    exact
      Complex.finiteAbelPlana_log_capCollarBoundaryContribution_eq_deletedBoundaryContribution_sub_verticalStripBoundarySum_owner
        N T hT hρ hdeleted_geometry hcont hdiff
  calc
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
            Complex.finiteAbelPlanaLogCapCollarBoundaryContribution N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact
        Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_unfold
          N w T ρ
    _ =
        Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ +
            (Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ -
              Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ) -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
      exact congrArg
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ + z -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
        hcap
    _ = 0 := by
      exact
        Complex.finiteAbelPlana_log_verticalStrip_add_deleted_sub_verticalStrip_sub_deleted
          (Complex.finiteAbelPlanaLogVerticalStripBoundarySum N w T ρ)
          (Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)

/-- Deep strip-decomposition Cauchy-Goursat theorem for the finite-radius
punctured Abel-Plana rectangle.

This is the owner statement still requiring the genuine planar proof: apply
Cauchy-Goursat on every finite vertical gap strip and on the upper/lower pieces
around each deleted disk, cancel all internal subdivision edges, and identify
the remaining oriented boundary, including endpoint semicircles and interior
deleted circles, with the named finite-radius punctured boundary. -/
theorem Complex.finiteAbelPlana_log_verticalStripDecomposition_cauchyGoursat_and_boundary
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
        Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
  exact
    ⟨Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_zero_owner
        N T hT hρ hdeleted_geometry hcont hdiff,
      Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary_owner
        N T hρ hdeleted_geometry hcont hdiff⟩

/-- The full finite-hole subdivision boundary is the named finite-radius
punctured boundary. -/
theorem Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary_public
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
  exact
    Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary_owner
      N T hρ hdeleted_geometry hcont hdiff

/-- Cauchy-Goursat vanishing of the full finite-hole subdivision boundary
before it is identified with the named finite-radius punctured boundary. -/
theorem Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ = 0 := by
  exact
    Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_zero_owner
      N T hT hρ hdeleted_geometry hcont hdiff

end

end LFunctions
end Boundary
