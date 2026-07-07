import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.FirstDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Regularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Calculus.Prelude
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Calculus.ByParts
import Mathlib.MeasureTheory.Integral.Bochner
/-!
# Reciprocal-density integral and calculus estimates

This file contains the main computational theorems for reciprocal-density integrals,
including integration bounds, by-parts identities, and calculus estimates.
-/

namespace Boundary
namespace LFunctions

open MeasureTheory

/-- Adjacent `Ioc` intervals split the finite reciprocal-density scalar
integral. -/
theorem real_integral_Ioc_log_two_add_div_sq_adjacent_split
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
      (∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2) +
        (∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2) := by
  let f : ℝ → ℝ := fun x => Real.log (2 + x) / x ^ 2
  have htwo_b : (2 : ℝ) ≤ b :=
    le_trans ha hab
  have hleft :
      ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..a, f x :=
    (intervalIntegral.integral_of_le ha).symm
  have hright :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 =
        ∫ x in a..b, f x :=
    (intervalIntegral.integral_of_le hab).symm
  have hall :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..b, f x :=
    (intervalIntegral.integral_of_le htwo_b).symm
  have hleft_cont : ContinuousOn f (Set.uIcc (2 : ℝ) a) := by
    exact fun x hx =>
    have hx_left : (2 : ℝ) ≤ x :=
      real_left_le_of_mem_uIcc_of_le ha hx
    have hx_pos : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_two hx_left)
    have harg_ne : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_trans (le_of_lt zero_lt_two) hx_left)
      exact ne_of_gt harg_pos
    (scalarReciprocalDensity_logTwoAdd_div_square_continuousAt
      hx_pos harg_ne).continuousWithinAt
  have hright_cont : ContinuousOn f (Set.uIcc a b) := by
    exact fun x hx =>
    have hx_left : a ≤ x :=
      real_left_le_of_mem_uIcc_of_le hab hx
    have hx_pos : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_two (le_trans ha hx_left))
    have harg_ne : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_trans (le_of_lt zero_lt_two) (le_trans ha hx_left))
      exact ne_of_gt harg_pos
    (scalarReciprocalDensity_logTwoAdd_div_square_continuousAt
      hx_pos harg_ne).continuousWithinAt
  have hleft_interval : IntervalIntegrable f volume (2 : ℝ) a :=
    hleft_cont.intervalIntegrable
  have hright_interval : IntervalIntegrable f volume a b :=
    hright_cont.intervalIntegrable
  have hadd :
      (∫ x in (2 : ℝ)..a, f x) + (∫ x in a..b, f x) =
        ∫ x in (2 : ℝ)..b, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      hleft_interval hright_interval
  exact Eq.trans hall
    (Eq.trans hadd.symm
      (congrArg₂ (fun u v : ℝ => u + v) hleft.symm hright.symm))

/-- Improper-tail comparison for `log(2+x)/x²` after the cutoff `2`.

This is the canonical real-analysis theorem behind the reciprocal-density
scalar estimate.  It is independent of zeta and is normally proved by
integration by parts:
`d(-log(2+x)/x) = log(2+x)/x² - 1/(x(2+x))`, followed by nonnegativity of the
remainder and endpoint evaluation at `x = 2`. -/
theorem real_integral_Ioc_log_two_add_div_sq_tail_bound_of_two_le
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  have htwo_le_b : (2 : ℝ) ≤ b :=
    le_trans ha hab
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (2 : ℝ) a)]
        (fun x : ℝ => Real.log (2 + x) / x ^ 2) :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        real_log_two_add_div_sq_nonneg_of_two_le (le_of_lt hx.1))
  have htail_split :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        (∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2) +
          (∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2) := by
    exact real_integral_Ioc_log_two_add_div_sq_adjacent_split ha hab
  have hleft_nonneg :
      0 ≤ ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 :=
    integral_nonneg_of_ae hnonneg
  have hle_tail :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
        ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 := by
    have hadd :
        ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
          (∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2) +
            (∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2) :=
      le_add_of_nonneg_left hleft_nonneg
    exact Eq.subst
      (motive := fun y : ℝ =>
        ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤ y)
      htail_split.symm
      hadd
  exact le_trans hle_tail
    (real_integral_Ioc_two_log_two_add_div_sq_tail_bound htwo_le_b)

theorem real_integral_Ioc_log_two_add_div_sq_tail_bound
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  exact
    real_integral_Ioc_log_two_add_div_sq_tail_bound_of_two_le
      ha hab

/-- Canonical real-variable comparison for the finite `log(2+x)/x²` integral.

On any interval beginning after `2`, the tail integral is bounded uniformly by
the full tail from `2` to infinity; that tail is below `Real.log 4`.  The
displayed height parameter is only used through `1 ≤ H`, hence
`Real.log 4 ≤ Real.log (3+H)`. -/
theorem real_integral_Ioc_log_two_add_div_sq_le_log_three_add_height
    {H a b : ℝ}
    (hH : (1 : ℝ) ≤ H)
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
      Real.log (3 + H) := by
  have htail :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤ Real.log 4 :=
    real_integral_Ioc_log_two_add_div_sq_tail_bound ha hab
  have hfour_le : (4 : ℝ) ≤ 3 + H := by
    calc
      (4 : ℝ) = 3 + 1 := by
        exact three_add_one_eq_four.symm
      _ ≤ 3 + H :=
        add_le_add_left hH 3
  have hlog_four_le : Real.log 4 ≤ Real.log (3 + H) := by
    have hfour_pos : (0 : ℝ) < 4 := by
      exact zero_lt_four
    exact Real.log_le_log hfour_pos hfour_le
  exact le_trans htail hlog_four_le

/-- Scalar calculus owner for the `log(2+x)/x` post-cutoff integral.

Proof route: on the post-cutoff interval, `2 ≤ x`, hence
`log(2+x)/x ≤ 2 * log(2+x)/(2+x)`, the derivative of
`(Real.log (2+x))^2`.  The fundamental theorem of calculus and endpoint
monotonicity then bound the finite interval by the right endpoint square. -/
theorem scalarReciprocalDensity_log_over_x_integral_bound_calculus
    (t : ℝ)
    (_ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ≤
      (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 := by
  have hN_two :
      (2 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    scalarReciprocalDensity_two_le_cutoff_real t
  have hNM_real :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact
    real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq
      hN_two hNM_real

/-- Scalar calculus owner for the `log(2+x)/x²` post-cutoff integral.

Proof route: use `Real.log_div_self_rpow_antitoneOn` for the decreasing
positive tail profile after the cutoff, or equivalently integrate by parts:
`∫ log(2+x)/x²` is bounded by the cutoff endpoint contribution plus the
integrable `1/(x(2+x))` remainder.  Since the cutoff is at least `2+|t|`, the
result is dominated by `Real.log (3 + ‖t‖)`. -/
theorem scalarReciprocalDensity_log_over_x_sq_integral_bound_calculus
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ^ 2 ≤
      Real.log (3 + ‖t‖) := by
  have hN_two :
      (2 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    scalarReciprocalDensity_two_le_cutoff_real t
  have hNM_real :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact
    real_integral_Ioc_log_two_add_div_sq_le_log_three_add_height
      ht hN_two hNM_real


/-- Finite-endpoint calculus bound for the `log(2+x)/x` contribution. -/
theorem scalarReciprocalDensity_log_over_x_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ≤
      (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 := by
  exact scalarReciprocalDensity_log_over_x_integral_bound_calculus t ht hNM

/-- Finite-endpoint calculus bound for the `log(2+x)/x^2` contribution. -/
theorem scalarReciprocalDensity_log_over_x_sq_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ^ 2 ≤
      Real.log (3 + ‖t‖) := by
  exact scalarReciprocalDensity_log_over_x_sq_integral_bound_calculus t ht hNM

/-- Pointwise algebraic split of the coarse reciprocal-density majorant.

The factor `x / |t|` contributes the `log(2+x)/x` term, using `1 ≤ |t|`; the
remaining `sqrt(1+|t|)` term contributes `log(2+x)/x²`. -/
theorem scalarReciprocalDensityMajorant_pointwise_split
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : 0 < x) :
    ((1 : ℝ) / x ^ 2) *
        (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + x) / x) +
        8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2) := by
  let L : ℝ := Real.log (2 + x)
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  let T : ℝ := ‖t‖
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one ht
  have hx_nonneg : 0 ≤ x :=
    le_of_lt hx
  have hx_sq_pos : 0 < x ^ 2 :=
    sq_pos_of_pos hx
  have hx_sq_nonneg : 0 ≤ x ^ 2 :=
    le_of_lt hx_sq_pos
  have hL_nonneg : 0 ≤ L := by
    have hone_le_two : (1 : ℝ) ≤ 2 := by
      calc
        (1 : ℝ) ≤ 1 + 1 := le_add_of_nonneg_right zero_le_one
        _ = 2 := by
          exact one_add_one_eq_two
    have htwo_le_two_add : (2 : ℝ) ≤ 2 + x :=
      calc
        (2 : ℝ) = 2 + 0 := by
          exact (add_zero 2).symm
        _ ≤ 2 + x :=
          add_le_add_left hx_nonneg 2
    exact Real.log_nonneg (le_trans hone_le_two htwo_le_two_add)
  have hS_nonneg : 0 ≤ S :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have height_nonneg : 0 ≤ (8 : ℝ) :=
    Nat.cast_nonneg 8
  have hweight_nonneg : 0 ≤ (1 : ℝ) / x ^ 2 := by
    exact div_nonneg zero_le_one hx_sq_nonneg
  have hfirst_ratio : x / T ≤ x := by
    have hmul_le : x ≤ x * T := by
      calc
        x = x * 1 := by
          exact (mul_one x).symm
        _ ≤ x * T :=
          mul_le_mul_of_nonneg_left ht hx_nonneg
    exact (div_le_iff₀ hT_pos).mpr hmul_le
  have hsum_le : (x / T) + S ≤ x + S :=
    add_le_add_right hfirst_ratio S
  have hmajor_le :
      8 * ((x / T) + S) * L ≤ 8 * (x + S) * L := by
    have hscaled :
        8 * ((x / T) + S) ≤ 8 * (x + S) :=
      mul_le_mul_of_nonneg_left hsum_le height_nonneg
    exact mul_le_mul_of_nonneg_right hscaled hL_nonneg
  have hweighted_major :
      ((1 : ℝ) / x ^ 2) * (8 * ((x / T) + S) * L) ≤
        ((1 : ℝ) / x ^ 2) * (8 * (x + S) * L) :=
    mul_le_mul_of_nonneg_left hmajor_le hweight_nonneg
  have hexpanded_bound :
      ((1 : ℝ) / x ^ 2) * (8 * (x + S) * L) =
        8 * (L / x) + 8 * S * (L / x ^ 2) := by
    calc
      ((1 : ℝ) / x ^ 2) * (8 * (x + S) * L) =
          ((1 : ℝ) / x ^ 2) * ((8 * x + 8 * S) * L) := by
        exact congrArg
          (fun y : ℝ => ((1 : ℝ) / x ^ 2) * (y * L))
          (mul_add 8 x S)
      _ = ((1 : ℝ) / x ^ 2) * (8 * x * L + 8 * S * L) := by
        exact congrArg
          (fun y : ℝ => ((1 : ℝ) / x ^ 2) * y)
          (add_mul (8 * x) (8 * S) L)
      _ =
          ((1 : ℝ) / x ^ 2) * (8 * x * L) +
            ((1 : ℝ) / x ^ 2) * (8 * S * L) := by
        exact mul_add ((1 : ℝ) / x ^ 2) (8 * x * L) (8 * S * L)
      _ = 8 * (L / x) +
            ((1 : ℝ) / x ^ 2) * (8 * S * L) := by
        have hx_ne : x ≠ 0 :=
          ne_of_gt hx
        have hx_sq_ne : x ^ 2 ≠ 0 :=
          pow_ne_zero 2 hx_ne
        have hfirst :
            ((1 : ℝ) / x ^ 2) * (8 * x * L) = 8 * (L / x) := by
          calc
            ((1 : ℝ) / x ^ 2) * (8 * x * L) =
                8 * L * (x / x ^ 2) := by
              let R : ℝ := (1 : ℝ) / x ^ 2
              calc
                R * (8 * x * L) = (8 * x * L) * R := by
                  exact mul_comm R (8 * x * L)
                _ = (8 * x) * (L * R) := by
                  exact mul_assoc (8 * x) L R
                _ = 8 * (x * (L * R)) := by
                  exact mul_assoc 8 x (L * R)
                _ = 8 * ((x * L) * R) := by
                  exact congrArg (fun y : ℝ => 8 * y) (mul_assoc x L R).symm
                _ = 8 * ((L * x) * R) := by
                  exact congrArg (fun y : ℝ => 8 * (y * R)) (mul_comm x L)
                _ = 8 * (L * (x * R)) := by
                  exact congrArg (fun y : ℝ => 8 * y) (mul_assoc L x R)
                _ = 8 * L * (x * R) := by
                  exact (mul_assoc 8 L (x * R)).symm
                _ = 8 * L * (x / x ^ 2) := by
                  exact congrArg (fun y : ℝ => 8 * L * y)
                    (div_eq_mul_one_div x (x ^ 2)).symm
            _ = 8 * L * (1 / x) := by
              have hx_cancel : x / x ^ 2 = 1 / x := by
                calc
                  x / x ^ 2 = x / (x * x) := by
                    exact congrArg (fun y : ℝ => x / y) (sq x)
                  _ = x⁻¹ := by
                    exact div_mul_cancel_left₀ hx_ne x
                  _ = 1 / x := by
                    exact (one_div x).symm
              exact congrArg (fun y : ℝ => 8 * L * y) hx_cancel
            _ = 8 * (L / x) := by
              calc
                8 * L * (1 / x) = 8 * (L * (1 / x)) := by
                  exact mul_assoc 8 L (1 / x)
                _ = 8 * (L / x) := by
                  exact congrArg (fun y : ℝ => 8 * y) (div_eq_mul_one_div L x).symm
        exact congrArg
          (fun y : ℝ => y + ((1 : ℝ) / x ^ 2) * (8 * S * L))
          hfirst
      _ = 8 * (L / x) + 8 * S * (L / x ^ 2) := by
        have hsecond :
            ((1 : ℝ) / x ^ 2) * (8 * S * L) =
              8 * S * (L / x ^ 2) := by
          calc
            ((1 : ℝ) / x ^ 2) * (8 * S * L) =
                8 * S * (L * ((1 : ℝ) / x ^ 2)) := by
              let R : ℝ := (1 : ℝ) / x ^ 2
              calc
                R * (8 * S * L) = (8 * S * L) * R := by
                  exact mul_comm R (8 * S * L)
                _ = (8 * S) * (L * R) := by
                  exact mul_assoc (8 * S) L R
            _ = 8 * S * (L / x ^ 2) := by
              exact congrArg
                (fun y : ℝ => 8 * S * y)
                (div_eq_mul_one_div L (x ^ 2)).symm
        exact congrArg (fun y : ℝ => 8 * (L / x) + y) hsecond
  exact le_trans hweighted_major (le_of_eq hexpanded_bound)

/-- Integral transport of the pointwise scalar split over the post-cutoff
interval. -/
theorem scalarReciprocalDensityMajorant_integral_split_le_components
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        (8 * (Real.log (2 + x) / x) +
          8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2)) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)
  let f : ℝ → ℝ := fun x =>
    ((1 : ℝ) / x ^ 2) *
      (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
  let g : ℝ → ℝ := fun x =>
    8 * (Real.log (2 + x) / x) +
      8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2)
  have hleft_pos : 0 < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t)
  have hf_cont : ContinuousOn f
      (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) := by
    exact fun x hx =>
    have hx_pos : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hleft_pos hx.1)
    have harg_ne : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_of_lt (lt_of_lt_of_le hleft_pos hx.1))
      exact ne_of_gt harg_pos
    have hreciprocal :
        ContinuousAt (fun y : ℝ => (1 : ℝ) / y ^ 2) x :=
      scalarReciprocalDensity_reciprocalSquare_continuousAt hx_pos
    have hquotient :
        ContinuousAt (fun y : ℝ => y / ‖t‖) x :=
      continuousAt_id.div_const ‖t‖
    have hshifted :
        ContinuousAt (fun y : ℝ => y / ‖t‖ + Real.sqrt (1 + ‖t‖)) x :=
      hquotient.add continuousAt_const
    have hweighted :
        ContinuousAt
          (fun y : ℝ => 8 * (y / ‖t‖ + Real.sqrt (1 + ‖t‖)))
          x :=
      continuousAt_const.mul hshifted
    have hlog :
        ContinuousAt (fun y : ℝ => Real.log (2 + y)) x :=
      scalarReciprocalDensity_logTwoAdd_continuousAt harg_ne
    (hreciprocal.mul (hweighted.mul hlog)).continuousWithinAt
  have hg_cont : ContinuousOn g
      (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) := by
    exact fun x hx =>
    have hx_pos : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hleft_pos hx.1)
    have harg_ne : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_of_lt (lt_of_lt_of_le hleft_pos hx.1))
      exact ne_of_gt harg_pos
    have hleft :
        ContinuousAt (fun y : ℝ => 8 * (Real.log (2 + y) / y)) x :=
      continuousAt_const.mul
        (scalarReciprocalDensity_logTwoAdd_div_self_continuousAt
          hx_pos harg_ne)
    have hright_base :
        ContinuousAt
          (fun y : ℝ => Real.log (2 + y) / y ^ 2)
          x :=
      scalarReciprocalDensity_logTwoAdd_div_square_continuousAt
        hx_pos harg_ne
    have hright :
        ContinuousAt
          (fun y : ℝ =>
            8 * Real.sqrt (1 + ‖t‖) *
              (Real.log (2 + y) / y ^ 2))
          x :=
      continuousAt_const.mul hright_base
    (hleft.add hright).continuousWithinAt
  have hf : Integrable f (volume.restrict s) :=
    (ContinuousOn.integrableOn_Icc hf_cont).mono_set Set.Ioc_subset_Icc_self
  have hg : Integrable g (volume.restrict s) :=
    (ContinuousOn.integrableOn_Icc hg_cont).mono_set Set.Ioc_subset_Icc_self
  have hle : f ≤ᵐ[volume.restrict s] g :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        scalarReciprocalDensityMajorant_pointwise_split
          t ht (scalarReciprocalDensity_Ioc_point_pos t hx))
  exact integral_mono_ae hf hg hle

/-- The component integral bounds imply the finite-endpoint bound for the
split scalar majorant. -/
theorem scalarReciprocalDensityMajorant_components_le_endpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hlog_over_x :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ≤
        (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2)
    (hlog_over_x_sq :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ^ 2 ≤
        Real.log (3 + ‖t‖)) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        (8 * (Real.log (2 + x) / x) +
          8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)
  let f : ℝ → ℝ := fun x => Real.log (2 + x) / x
  let g : ℝ → ℝ := fun x => Real.log (2 + x) / x ^ 2
  let A : ℝ := (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2
  let B : ℝ := Real.log (3 + ‖t‖)
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  have hleft_pos : 0 < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t)
  have hf_cont : ContinuousOn (fun x => 8 * f x)
      (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :=
    fun x hx =>
    have hx_pos : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hleft_pos hx.1)
    have harg_ne : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_of_lt (lt_of_lt_of_le hleft_pos hx.1))
      exact ne_of_gt harg_pos
    (continuousAt_const.mul
      (scalarReciprocalDensity_logTwoAdd_div_self_continuousAt
        hx_pos harg_ne)).continuousWithinAt
  have hg_cont : ContinuousOn (fun x => 8 * S * g x)
      (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :=
    fun x hx =>
    have hx_pos : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hleft_pos hx.1)
    have harg_ne : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_of_lt (lt_of_lt_of_le hleft_pos hx.1))
      exact ne_of_gt harg_pos
    have hbase :
        ContinuousAt
          (fun y : ℝ => Real.log (2 + y) / y ^ 2)
          x :=
      scalarReciprocalDensity_logTwoAdd_div_square_continuousAt
        hx_pos harg_ne
    (continuousAt_const.mul hbase).continuousWithinAt
  have hf : Integrable (fun x => 8 * f x) (volume.restrict s) :=
    (ContinuousOn.integrableOn_Icc hf_cont).mono_set Set.Ioc_subset_Icc_self
  have hg : Integrable (fun x => 8 * S * g x) (volume.restrict s) :=
    (ContinuousOn.integrableOn_Icc hg_cont).mono_set Set.Ioc_subset_Icc_self
  have hsum_eq :
      (∫ x in s, (8 * f x + 8 * S * g x)) =
        (∫ x in s, 8 * f x) + ∫ x in s, 8 * S * g x :=
    integral_add hf hg
  have hf_scale :
      (∫ x in s, 8 * f x) = 8 * ∫ x in s, f x :=
    integral_mul_left 8 f
  have hg_scale :
      (∫ x in s, 8 * S * g x) = (8 * S) * ∫ x in s, g x :=
    integral_mul_left (8 * S) g
  have height_nonneg : 0 ≤ (8 : ℝ) := by
    exact Nat.cast_nonneg 8
  have hS_nonneg : 0 ≤ S :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hheightS_nonneg : 0 ≤ 8 * S :=
    mul_nonneg height_nonneg hS_nonneg
  have hfirst :
      (∫ x in s, 8 * f x) ≤ 8 * A := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ 8 * A)
      hf_scale.symm
      (mul_le_mul_of_nonneg_left hlog_over_x height_nonneg)
  have hsecond :
      (∫ x in s, 8 * S * g x) ≤ (8 * S) * B := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ (8 * S) * B)
      hg_scale.symm
      (mul_le_mul_of_nonneg_left hlog_over_x_sq hheightS_nonneg)
  have hsum_bound :
      (∫ x in s, 8 * f x) + ∫ x in s, 8 * S * g x ≤
        8 * A + (8 * S) * B :=
    add_le_add hfirst hsecond
  have htarget_eq :
      8 * A + (8 * S) * B =
        8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
          8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
    rfl
  exact Eq.subst
    (motive := fun y : ℝ =>
      y ≤
        8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
          8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖))
    hsum_eq.symm
    (le_trans hsum_bound (le_of_eq htarget_eq))

/-- Algebraic split of the coarse reciprocal-density scalar majorant into the
two real calculus integrals it requires. -/
theorem scalarReciprocalDensityMajorant_integral_split_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hlog_over_x :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ≤
        (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2)
    (hlog_over_x_sq :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ^ 2 ≤
        Real.log (3 + ‖t‖)) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  exact
    le_trans
      (scalarReciprocalDensityMajorant_integral_split_le_components t ht hNM)
      (scalarReciprocalDensityMajorant_components_le_endpoint_bound
        t ht hNM hlog_over_x hlog_over_x_sq)

/-- Finite-endpoint real calculus bound for the coarse reciprocal-density
majorant.

The coarse first-derivative partial-sum majorant contains an `x / |t|` term, so
integrating it against `x⁻²` produces logarithmic growth in the right endpoint.
This is the honest scalar comparison; the uniform Abel/Euler-Maclaurin integral
bound must use the oscillatory cancellation theorem below, not this coarse
majorant alone. -/
theorem scalarReciprocalDensityMajorant_finiteEndpoint_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  exact
    scalarReciprocalDensityMajorant_integral_split_bound
      t ht hNM
      (scalarReciprocalDensity_log_over_x_integral_bound t ht hNM)
      (scalarReciprocalDensity_log_over_x_sq_integral_bound t ht hNM)

/-- Finite real calculus estimate for the scalar reciprocal-density majorant.

This wrapper keeps the older local name while the owner theorem records the
finite-endpoint growth explicitly. -/
theorem reciprocalDensityIntegral_scalar_majorant_finite_endpoint_bound_calculus
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  exact scalarReciprocalDensityMajorant_finiteEndpoint_integral_bound t ht hNM

end LFunctions
end Boundary
