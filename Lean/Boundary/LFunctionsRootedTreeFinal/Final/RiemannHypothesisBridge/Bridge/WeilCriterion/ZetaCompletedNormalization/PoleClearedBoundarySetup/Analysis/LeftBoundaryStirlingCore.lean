import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Analysis.LeftBoundaryArguments
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.Owner
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Boundary-line Gamma analysis and Abel-Plana assembly

## Helper lemmas for numeric bounds
-/

namespace Boundary
namespace LFunctions

/-- Helper: Large denominator positive. -/
private lemma ten_billion_pos : (0 : ℝ) < 10000000000 := by
  exact Nat.cast_pos.mpr (Nat.succ_pos 9999999999)

/-- Helper: Euler's constant approximation bound. -/
private lemma euler_approx_le_three : (27182818286 : ℕ) ≤ 3 * 10000000000 := by
  exact Nat.le.intro (show 27182818286 + 2817181714 = 3 * 10000000000 by rfl)

end LFunctions
end Boundary

/-!
# Boundary-line Gamma analysis and Abel-Plana assembly

This file owns the specific left-boundary applications of vertical Stirling estimates,
the concrete boundary-line zeta computations, and the Abel/Euler-Maclaurin infrastructure
for finite oscillatory sums along the critical line.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The numerator vertical line for the left-boundary quotient, before the `π`
normalization is attached.

This is the canonical classical special-function input: vertical Stirling for
`Γ(1/2 - i t/2)` with the exponential envelope needed on the left boundary;
cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_leftBoundary_numerator_core_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
  exact match verticalComplexGammaStirling_fixedRealPart_core_bounds hbranch (1 / 2) with
    | ⟨A, hA_pos, hA⟩ =>
      ⟨A, hA_pos, fun t ht => by
  have htail : (1 / 2 : ℝ) ≤ ‖-t / 2‖ :=
    neg_half_norm_ge_one_half_of_one_le_norm ht
  have hbound :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) *
          (1 + ‖-t / 2‖) ^ ((1 / 2 : ℝ) - 1 / 2) :=
    (hA (-t / 2) htail).1
  have harg :
      Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2) =
        Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I) := by
    exact congrArg Complex.Gamma
      (leftBoundary_numerator_complexGamma_argument_eq_fixedRealPart t)
  have hpow :
      (1 + ‖-t / 2‖) ^ ((1 / 2 : ℝ) - 1 / 2) = 1 := by
    have hexponent :
        ((1 / 2 : ℝ) - 1 / 2) = 0 :=
      sub_self (1 / 2 : ℝ)
    exact Eq.subst
      (motive := fun x : ℝ => (1 + ‖-t / 2‖) ^ x = 1)
      hexponent.symm
      (Real.rpow_zero (1 + ‖-t / 2‖))
  have hnorm : ‖-t / 2‖ = ‖t‖ / 2 := by
    have hneg_div : -t / 2 = -(t / 2) := by
      exact neg_div (2 : ℝ) t
    have htwo_nonneg : (0 : ℝ) ≤ 2 :=
      le_of_lt zero_lt_two
    calc
      ‖-t / 2‖ = ‖-(t / 2)‖ := by
        exact congrArg norm hneg_div
      _ = ‖t / 2‖ := by
        exact norm_neg (t / 2)
      _ = ‖t‖ / ‖(2 : ℝ)‖ := by
        exact norm_div t 2
      _ = ‖t‖ / 2 := by
        exact congrArg (fun x : ℝ => ‖t‖ / x)
          (Real.norm_of_nonneg htwo_nonneg)
  have hquarter : (Real.pi / 2) / 2 = Real.pi / 4 := by
    have hdiv :
        (Real.pi / 2) / 2 = Real.pi / ((2 : ℝ) * 2) :=
      div_div Real.pi 2 2
    have htwo_mul_two : (2 : ℝ) * 2 = 4 := by
      calc
        (2 : ℝ) * 2 = 2 + 2 := by
          exact two_mul 2
        _ = 4 := by
          exact two_add_two_eq_four
    exact hdiv.trans (congrArg (fun x : ℝ => Real.pi / x) htwo_mul_two)
  have hexponent :
      -(Real.pi / 2) * (‖t‖ / 2) = -(Real.pi / 4) * ‖t‖ := by
    calc
      -(Real.pi / 2) * (‖t‖ / 2) = -((Real.pi / 2) * (‖t‖ / 2)) := by
        exact neg_mul (Real.pi / 2) (‖t‖ / 2)
      _ = -((Real.pi / 2) * ‖t‖ / 2) := by
        exact congrArg (fun x : ℝ => -x) (mul_div_assoc' (Real.pi / 2) ‖t‖ 2)
      _ = -(((Real.pi / 2) / 2) * ‖t‖) := by
        exact congrArg (fun x : ℝ => -x) (div_mul_eq_mul_div₀ (Real.pi / 2) ‖t‖ 2).symm
      _ = -((Real.pi / 4) * ‖t‖) := by
        exact congrArg (fun x : ℝ => -(x * ‖t‖)) hquarter
      _ = -(Real.pi / 4) * ‖t‖ := by
        exact (neg_mul (Real.pi / 4) ‖t‖).symm
  have hexp :
      Real.exp (-(Real.pi / 2) * ‖-t / 2‖) =
        Real.exp (-(Real.pi / 4) * ‖t‖) := by
    exact congrArg Real.exp
      (Eq.trans
        (congrArg (fun x : ℝ => -(Real.pi / 2) * x) hnorm)
        hexponent)
  have hbound' :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) * 1 := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
          A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) * x)
      hpow
      hbound
  have hbound'' :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) := by
    calc
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
          A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) * 1 := hbound'
      _ = A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) := by
        exact mul_one _
  have hbound_final :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
    have hAexp :
        A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) =
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
      exact congrArg (fun x : ℝ => A * x) hexp
    exact le_trans hbound'' (le_of_eq hAexp)
  have hbound_target :
      ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
        A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
    calc
      ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ =
          ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ := by
        exact congrArg norm harg
      _ ≤ A * Real.exp (-(Real.pi / 4) * ‖t‖) := hbound_final
  exact hbound_target
  ⟩

/-- The denominator vertical line for the left-boundary quotient, before the `π`
normalization is attached.

This is the canonical classical special-function input: the reciprocal vertical
Stirling estimate for `Γ(i t/2)`; cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_leftBoundary_denominator_inv_core_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(Complex.Gamma (((t : ℂ) * Complex.I) / 2))⁻¹‖ ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
  exact match verticalComplexGammaStirling_fixedRealPart_core_bounds hbranch 0 with
    | ⟨B, hB_pos, hB⟩ =>
      ⟨B, hB_pos, fun t ht => by
  have htail : (1 / 2 : ℝ) ≤ ‖t / 2‖ :=
    half_norm_ge_one_half_of_one_le_norm ht
  have hbound :
      ‖(Complex.Gamma (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I))⁻¹‖ ≤
        B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
          (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) :=
    (hB (t / 2) htail).2
  have harg :
      Complex.Gamma (((t : ℂ) * Complex.I) / 2) =
        Complex.Gamma (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I) := by
    exact congrArg Complex.Gamma
      (leftBoundary_denominator_complexGamma_argument_eq_fixedRealPart t)
  have hnorm_half : ‖t / 2‖ = ‖t‖ / 2 := by
    have htwo_nonneg : (0 : ℝ) ≤ 2 :=
      le_of_lt zero_lt_two
    calc
      ‖t / 2‖ = ‖t‖ / ‖(2 : ℝ)‖ := by
        exact norm_div t 2
      _ = ‖t‖ / 2 := by
        exact congrArg (fun x : ℝ => ‖t‖ / x)
          (Real.norm_of_nonneg htwo_nonneg)
  have hquarter : (Real.pi / 2) / 2 = Real.pi / 4 := by
    have hdiv :
        (Real.pi / 2) / 2 = Real.pi / ((2 : ℝ) * 2) :=
      div_div Real.pi 2 2
    have htwo_mul_two : (2 : ℝ) * 2 = 4 := by
      calc
        (2 : ℝ) * 2 = 2 + 2 := by
          exact two_mul 2
        _ = 4 := by
          exact two_add_two_eq_four
    exact hdiv.trans (congrArg (fun x : ℝ => Real.pi / x) htwo_mul_two)
  have hexponent :
      (Real.pi / 2) * (‖t‖ / 2) = (Real.pi / 4) * ‖t‖ := by
    calc
      (Real.pi / 2) * (‖t‖ / 2) = (Real.pi / 2) * ‖t‖ / 2 := by
        exact mul_div_assoc' (Real.pi / 2) ‖t‖ 2
      _ = ((Real.pi / 2) / 2) * ‖t‖ := by
        exact (div_mul_eq_mul_div₀ (Real.pi / 2) ‖t‖ 2).symm
      _ = (Real.pi / 4) * ‖t‖ := by
        exact congrArg (fun x : ℝ => x * ‖t‖) hquarter
  have hexp :
      Real.exp ((Real.pi / 2) * ‖t / 2‖) =
        Real.exp ((Real.pi / 4) * ‖t‖) := by
    exact congrArg Real.exp
      (Eq.trans
        (congrArg (fun x : ℝ => (Real.pi / 2) * x) hnorm_half)
        hexponent)
  have hbase_nonneg : 0 ≤ 1 + ‖t / 2‖ :=
    add_nonneg zero_le_one (norm_nonneg (t / 2))
  have hhalf_le : ‖t‖ / 2 ≤ ‖t‖ :=
    div_le_self (norm_nonneg t) one_le_two
  have hbase_le : 1 + ‖t / 2‖ ≤ 1 + ‖t‖ := by
    exact add_le_add_left
      (Eq.subst
        (motive := fun x : ℝ => x ≤ ‖t‖)
        hnorm_half.symm
        hhalf_le)
      1
  have hpow_le :
      (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤ Real.sqrt (1 + ‖t / 2‖) := by
    have hexponent :
        ((1 / 2 : ℝ) - 0) = 1 / 2 :=
      sub_zero (1 / 2 : ℝ)
    have hrpow :
        (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) =
          Real.sqrt (1 + ‖t / 2‖) := by
      have hsqrt :
          (1 + ‖t / 2‖) ^ (1 / 2 : ℝ) = Real.sqrt (1 + ‖t / 2‖) := by
        exact (Real.sqrt_eq_rpow (1 + ‖t / 2‖)).symm
      exact Eq.trans
        (congrArg (fun x : ℝ => (1 + ‖t / 2‖) ^ x) hexponent)
        hsqrt
    exact le_of_eq hrpow
  have hsqrt :
      (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤ Real.sqrt (1 + ‖t‖) := by
    exact le_trans hpow_le (Real.sqrt_le_sqrt hbase_le)
  have hscaled :
      B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
          (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤
        B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
    have hstep1 :
        B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
            (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤
          B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
            Real.sqrt (1 + ‖t / 2‖) := by
      exact mul_le_mul_of_nonneg_left hpow_le
        (mul_nonneg (le_of_lt hB_pos) (le_of_lt (Real.exp_pos _)))
    have hstep2 :
        B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
            Real.sqrt (1 + ‖t / 2‖) ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
      have hexp_le :
          B * Real.exp ((Real.pi / 2) * ‖t / 2‖) ≤
            B * Real.exp ((Real.pi / 4) * ‖t‖) := by
        have hmul :
            Real.exp ((Real.pi / 2) * ‖t / 2‖) * B ≤
              Real.exp ((Real.pi / 4) * ‖t‖) * B := by
          calc
            Real.exp ((Real.pi / 2) * ‖t / 2‖) * B = B * Real.exp ((Real.pi / 2) * ‖t / 2‖) := by
              exact mul_comm _ _
            _ ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) := by
              exact (mul_le_mul_left hB_pos).2 (le_of_eq hexp)
            _ = Real.exp ((Real.pi / 4) * ‖t‖) * B := by
              exact mul_comm _ _
        calc
          B * Real.exp ((Real.pi / 2) * ‖t / 2‖) = Real.exp ((Real.pi / 2) * ‖t / 2‖) * B := by
            exact mul_comm _ _
          _ ≤ Real.exp ((Real.pi / 4) * ‖t‖) * B := hmul
          _ = B * Real.exp ((Real.pi / 4) * ‖t‖) := by
            exact mul_comm _ _
      have hsqrt_le :
          Real.sqrt (1 + ‖t / 2‖) ≤ Real.sqrt (1 + ‖t‖) :=
        Real.sqrt_le_sqrt hbase_le
      have hright_nonneg :
          0 ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) :=
        mul_nonneg (le_of_lt hB_pos) (le_of_lt (Real.exp_pos _))
      exact mul_le_mul hexp_le hsqrt_le (Real.sqrt_nonneg _) hright_nonneg
    calc
      B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
          (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤
        B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
          Real.sqrt (1 + ‖t / 2‖) := hstep1
      _ ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := hstep2
  have hbound_target :
      ‖(Complex.Gamma (((t : ℂ) * Complex.I) / 2))⁻¹‖ ≤
        B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
    calc
      ‖(Complex.Gamma (((t : ℂ) * Complex.I) / 2))⁻¹‖ =
          ‖(Complex.Gamma (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I))⁻¹‖ := by
        exact congrArg (fun x : ℂ => ‖x⁻¹‖) harg
      _ ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
        exact le_trans hbound hscaled
  exact hbound_target⟩

/-- The real part of the numerator `π`-normalizing exponent is `-1/2`. -/
theorem leftBoundary_numerator_piExponent_re
    (t : ℝ) :
    (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2).re = -(1 / 2 : ℝ) := by
  calc
    (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2).re =
        (-((1 : ℂ) - (t : ℂ) * Complex.I)).re / 2 := by
      exact Complex.div_ofReal_re (-((1 : ℂ) - (t : ℂ) * Complex.I)) 2
    _ = -(((1 : ℂ) - (t : ℂ) * Complex.I).re) / 2 := by
      exact congrArg (fun x : ℝ => x / 2)
        (Complex.neg_re ((1 : ℂ) - (t : ℂ) * Complex.I))
    _ = -(1 / 2 : ℝ) := by
      have hre_one : (((1 : ℂ) - (t : ℂ) * Complex.I).re) = 1 := by
        calc
          (((1 : ℂ) - (t : ℂ) * Complex.I).re) =
              (1 : ℂ).re - ((t : ℂ) * Complex.I).re := by
            exact Complex.sub_re (1 : ℂ) ((t : ℂ) * Complex.I)
          _ = 1 - ((t : ℂ) * Complex.I).re := by
            exact congrArg (fun x : ℝ => x - ((t : ℂ) * Complex.I).re) Complex.one_re
          _ = 1 - ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) := by
            exact congrArg (fun x : ℝ => 1 - x)
              (Complex.mul_re (t : ℂ) Complex.I)
          _ = 1 - (t * 0 - 0 * 1) := by
            rfl
          _ = 1 := by
            calc
              1 - (t * 0 - 0 * 1) = 1 - (0 - 0 * 1) := by
                exact congrArg (fun x : ℝ => 1 - (x - 0 * 1)) (mul_zero t)
              _ = 1 - (0 - 0) := by
                exact congrArg (fun x : ℝ => 1 - (0 - x)) (zero_mul 1)
              _ = 1 - 0 := by
                exact congrArg (fun x : ℝ => 1 - x) (sub_zero 0)
              _ = 1 :=
                sub_zero 1
      calc
        -(((1 : ℂ) - (t : ℂ) * Complex.I).re) / 2 =
            -1 / 2 := by
          exact congrArg (fun x : ℝ => -x / 2) hre_one
        _ = -(1 / 2 : ℝ) := by
          exact neg_div (2 : ℝ) 1

  /-- The numerator `π`-normalizing factor is bounded by `1`; its constant
  contribution is absorbed into the Stirling constant. -/
theorem norm_leftBoundary_numerator_piFactor_le_one
    (t : ℝ) :
    ‖((π : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))‖ ≤ 1 := by
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hpi_one_le : (1 : ℝ) ≤ π := by
    have htwo_le_three : (2 : ℝ) ≤ 3 := by
      calc
        (2 : ℝ) ≤ 2 + 1 :=
          le_add_of_nonneg_right zero_le_one
        _ = 3 := by
          exact two_add_one_eq_three
    exact le_trans one_le_two
      (le_trans htwo_le_three Real.pi_gt_three.le)
  have hnorm_eq :
      ‖((π : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))‖ =
        π ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖((π : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))‖ =
          Complex.abs ((π : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)) := by
        exact Complex.norm_eq_abs
          ((π : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))
      _ = π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ).re := by
        exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos
          (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)
      _ = π ^ (-(1 / 2 : ℝ)) := by
        exact congrArg (fun x : ℝ => π ^ x) (leftBoundary_numerator_piExponent_re t)
  have hexponent_nonpos : (-(1 / 2 : ℝ)) ≤ 0 := by
    exact neg_nonpos.mpr
      (div_nonneg zero_le_one zero_le_two)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1)
    hnorm_eq.symm
    (Real.rpow_le_one_of_one_le_of_nonpos hpi_one_le hexponent_nonpos)

/-- The real part of the denominator `π`-normalizing exponent is `0`. -/
theorem leftBoundary_denominator_piExponent_re
    (t : ℝ) :
    (-((t : ℂ) * Complex.I) / 2).re = 0 := by
  calc
    (-((t : ℂ) * Complex.I) / 2).re =
        (-((t : ℂ) * Complex.I)).re / 2 := by
      exact Complex.div_ofReal_re (-((t : ℂ) * Complex.I)) 2
    _ = -(((t : ℂ) * Complex.I).re) / 2 := by
      exact congrArg (fun x : ℝ => x / 2)
        (Complex.neg_re ((t : ℂ) * Complex.I))
    _ = -(t * 0 - 0 * 1) / 2 := by
      exact congrArg (fun x : ℝ => -x / 2)
        (calc
          (((t : ℂ) * Complex.I).re) =
              (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
            exact Complex.mul_re (t : ℂ) Complex.I
          _ = t * 0 - 0 * 1 := by
            rfl)
    _ = 0 := by
      calc
        -(t * 0 - 0 * 1) / 2 = -(0 - 0 * 1) / 2 := by
          exact congrArg (fun x : ℝ => -(x - 0 * 1) / 2) (mul_zero t)
        _ = -(0 - 0) / 2 := by
          exact congrArg (fun x : ℝ => -(0 - x) / 2) (zero_mul 1)
        _ = -0 / 2 := by
          exact congrArg (fun x : ℝ => -x / 2) (sub_zero 0)
        _ = 0 / 2 := by
          exact congrArg (fun x : ℝ => x / 2) (neg_zero)
        _ = 0 :=
          zero_div 2

/-- The denominator `π`-normalizing factor has norm one on the left-boundary
vertical line. -/
theorem norm_leftBoundary_denominator_piFactor_eq_one
    (t : ℝ) :
    ‖((π : ℂ) ^ (-((t : ℂ) * Complex.I) / 2 : ℂ))‖ = 1 := by
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  calc
    ‖((π : ℂ) ^ (-((t : ℂ) * Complex.I) / 2 : ℂ))‖ =
        Complex.abs ((π : ℂ) ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)) := by
      exact Complex.norm_eq_abs
        ((π : ℂ) ^ (-((t : ℂ) * Complex.I) / 2 : ℂ))
    _ = π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ).re := by
      exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos
        (-((t : ℂ) * Complex.I) / 2 : ℂ)
    _ = π ^ (0 : ℝ) := by
      exact congrArg (fun x : ℝ => π ^ x)
        (leftBoundary_denominator_piExponent_re t)
    _ = 1 := by
      exact Real.rpow_zero π

/-- The denominator `π`-normalizing factor is nonzero on the left-boundary
vertical line. -/
theorem leftBoundary_denominator_piFactor_ne_zero
    (t : ℝ) :
    ((π : ℂ) ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)) ≠ 0 := by
  intro hzero
  have hnorm_zero :
      ‖((π : ℂ) ^ (-((t : ℂ) * Complex.I) / 2 : ℂ))‖ = 0 := by
    calc
      ‖((π : ℂ) ^ (-((t : ℂ) * Complex.I) / 2 : ℂ))‖ = ‖(0 : ℂ)‖ := by
        exact congrArg norm hzero
      _ = 0 := by
        exact norm_zero
  have hone_zero : (1 : ℝ) = 0 := by
    calc
      (1 : ℝ) = ‖((π : ℂ) ^ (-((t : ℂ) * Complex.I) / 2 : ℂ))‖ := by
        exact (norm_leftBoundary_denominator_piFactor_eq_one t).symm
      _ = 0 := hnorm_zero
  exact one_ne_zero hone_zero

/-- Attach the numerator `π`-normalization to the canonical vertical `Complex.Gamma`
Stirling estimate. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound_of_core
    (hcore :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
            A * Real.exp (-(Real.pi / 4) * ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
  exact match hcore with
    | ⟨A, hA_pos, hA⟩ =>
      ⟨A, hA_pos, fun t ht => by
        have hpi_le_one :
            ‖((π : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))‖ ≤ 1 :=
          norm_leftBoundary_numerator_piFactor_le_one t
        have hgamma_bound :
            ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
              A * Real.exp (-(Real.pi / 4) * ‖t‖) :=
          hA t ht
        have htarget_nonneg :
            0 ≤ A * Real.exp (-(Real.pi / 4) * ‖t‖) :=
          mul_nonneg (le_of_lt hA_pos) (le_of_lt (Real.exp_pos _))
        calc
          ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ =
              ‖((π : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))‖ *
                ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ := by
            exact norm_mul
              ((π : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))
              (Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2))
          _ ≤ 1 * (A * Real.exp (-(Real.pi / 4) * ‖t‖)) := by
            exact mul_le_mul hpi_le_one hgamma_bound (norm_nonneg _) zero_le_one
          _ = A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
            exact one_mul (A * Real.exp (-(Real.pi / 4) * ‖t‖))
      ⟩

/-- Attach the denominator `π`-normalization to the canonical reciprocal vertical
`Complex.Gamma` Stirling estimate. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound_of_core
    (hcore :
      ∃ B : ℝ,
        0 < B ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖(Complex.Gamma (((t : ℂ) * Complex.I) / 2))⁻¹‖ ≤
            B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖)) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
  rcases hcore with ⟨B, hB_pos, hB⟩
  refine ⟨B, hB_pos, ?_⟩
  intro t ht
  let P : ℂ := (π : ℂ) ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)
  let G : ℂ := Complex.Gamma (((t : ℂ) * Complex.I) / 2)
  have hP_ne : P ≠ 0 :=
    leftBoundary_denominator_piFactor_ne_zero t
  have hP_norm_one : ‖P‖ = (1 : ℝ) :=
    norm_leftBoundary_denominator_piFactor_eq_one t
  have hraw :
      ‖G⁻¹‖ ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) :=
    hB t ht
  have hnorm_eq :
      ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ =
        ‖G⁻¹‖ := by
    calc
      ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ =
          ‖(P * G)⁻¹‖ := by
        rfl
      _ = ‖G⁻¹ * P⁻¹‖ := by
        exact congrArg norm (mul_inv_rev P G)
      _ = ‖P⁻¹ * G⁻¹‖ := by
        exact congrArg norm (mul_comm G⁻¹ P⁻¹)
      _ = ‖P⁻¹‖ * ‖G⁻¹‖ := by
        exact norm_mul P⁻¹ G⁻¹
      _ = ‖P‖⁻¹ * ‖G⁻¹‖ := by
        exact congrArg (fun x : ℝ => x * ‖G⁻¹‖) (norm_inv P)
      _ = 1⁻¹ * ‖G⁻¹‖ := by
        exact congrArg (fun x : ℝ => x⁻¹ * ‖G⁻¹‖) hP_norm_one
      _ = 1 * ‖G⁻¹‖ := by
        exact congrArg (fun x : ℝ => x * ‖G⁻¹‖) (inv_one : (1 : ℝ)⁻¹ = 1)
      _ = ‖G⁻¹‖ := by
        exact one_mul ‖G⁻¹‖
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖))
    hnorm_eq.symm
    hraw

/-- Vertical Stirling upper bound for the named numerator in the unfolded left-boundary
Gamma quotient.

This is one of the exact classical special-function inputs: Stirling on the vertical
line `((1 - it) / 2)`, including the `π` normalization; cf. DLMF §5.11. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
  exact
    twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound_of_core
      (verticalComplexGammaStirling_leftBoundary_numerator_core_bound hbranch)

/-- Vertical Stirling reciprocal bound for the named denominator in the unfolded
left-boundary Gamma quotient.

This is the matching exact classical special-function input: Stirling on the vertical
line `(it / 2)`, inverted and normalized so the quotient algebra has the expected
square-root growth; cf. DLMF §5.11. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
  exact
    twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound_of_core
      (verticalComplexGammaStirling_leftBoundary_denominator_inv_core_bound hbranch)

/-- Algebraic quotient estimate obtained from the numerator bound and denominator
reciprocal bound.  The exponential factors cancel, leaving the square-root envelope. -/
theorem unfoldedGammaℝLeftBoundaryRatioRealParam_sqrt_growth_bound_of_numerator_and_denominator
    (hnum :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤
            A * Real.exp (-(Real.pi / 4) * ‖t‖))
    (hden :
      ∃ B : ℝ,
        0 < B ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
            B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match hnum, hden with
    | ⟨Anum, hAnum_pos, hAnum⟩, ⟨Bden, hBden_pos, hBden⟩ =>
      ⟨Anum * Bden, mul_pos hAnum_pos hBden_pos, fun t ht => by
  let Eminus : ℝ := Real.exp (-(Real.pi / 4) * ‖t‖)
  let Eplus : ℝ := Real.exp ((Real.pi / 4) * ‖t‖)
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  have hnum_bound :
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤ Anum * Eminus :=
    hAnum t ht
  have hden_bound :
      ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
        Bden * Eplus * S :=
    hBden t ht
  have hden_inv_nonneg :
      0 ≤ ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ :=
    norm_nonneg _
  have hquot_eq :
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ =
        ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ *
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ := by
    calc
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ =
          ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t /
            unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ :=
        norm_unfoldedGammaℝLeftBoundaryRatioRealParam_eq_named_quotient t
      _ = ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t *
            (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ := by
        rfl
      _ = ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ *
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ := by
        exact norm_mul
          (unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t)
          (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹
  have hmul_bound :
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ *
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
        (Anum * Eminus) * (Bden * Eplus * S) :=
    mul_le_mul hnum_bound hden_bound hden_inv_nonneg
      (mul_nonneg (le_of_lt hAnum_pos) (Real.exp_pos _).le)
  have hexp_cancel :
      Eminus * Eplus = 1 := by
    have hsum_exp :
        (-(Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖) = 0 := by
      have hneg :
          -(Real.pi / 4) * ‖t‖ =
            -((Real.pi / 4) * ‖t‖) := by
        exact (neg_mul_eq_neg_mul (Real.pi / 4) ‖t‖).symm
      calc
        (-(Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖) =
            -((Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖) := by
          exact congrArg
            (fun x : ℝ => x + ((Real.pi / 4) * ‖t‖))
            hneg
        _ = 0 := by
          exact neg_add_cancel ((Real.pi / 4) * ‖t‖)
    calc
      Eminus * Eplus =
          Real.exp ((-(Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖)) := by
        exact (Real.exp_add (-(Real.pi / 4) * ‖t‖) ((Real.pi / 4) * ‖t‖)).symm
      _ = Real.exp 0 := by
        exact congrArg Real.exp hsum_exp
      _ = 1 := Real.exp_zero
  have htarget_eq :
      (Anum * Eminus) * (Bden * Eplus * S) = (Anum * Bden) * S := by
    have hcomm :
        (Anum * Eminus) * (Bden * Eplus * S) =
          (Anum * Bden) * (Eminus * Eplus) * S := by
      calc
        (Anum * Eminus) * (Bden * Eplus * S) =
            Anum * (Eminus * (Bden * Eplus * S)) := by
          exact mul_assoc Anum Eminus (Bden * Eplus * S)
        _ = Anum * (Bden * (Eminus * Eplus * S)) := by
          exact congrArg (fun x : ℝ => Anum * x)
            (calc
              Eminus * (Bden * Eplus * S) =
                  Eminus * (Bden * (Eplus * S)) := by
                exact congrArg (fun x : ℝ => Eminus * x)
                  (mul_assoc Bden Eplus S)
              _ = Bden * (Eminus * (Eplus * S)) := by
                exact mul_left_comm Eminus Bden (Eplus * S)
              _ = Bden * ((Eminus * Eplus) * S) := by
                exact congrArg (fun x : ℝ => Bden * x)
                  (mul_assoc Eminus Eplus S).symm)
        _ = (Anum * Bden) * (Eminus * Eplus * S) := by
          exact (mul_assoc Anum Bden (Eminus * Eplus * S)).symm
        _ = (Anum * Bden) * ((Eminus * Eplus) * S) := by
          rfl
        _ = (Anum * Bden) * (Eminus * Eplus) * S := by
          exact (mul_assoc (Anum * Bden) (Eminus * Eplus) S).symm
    calc
      (Anum * Eminus) * (Bden * Eplus * S) =
          (Anum * Bden) * (Eminus * Eplus) * S :=
        hcomm
      _ = (Anum * Bden) * 1 * S := by
        exact congrArg (fun x : ℝ => (Anum * Bden) * x * S) hexp_cancel
      _ = (Anum * Bden) * S := by
        exact congrArg (fun x : ℝ => x * S)
          (mul_one (Anum * Bden))
  exact Eq.subst
    (motive := fun x : ℝ => ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤ x)
    htarget_eq
    (Eq.subst
      (motive := fun x : ℝ => x ≤ (Anum * Eminus) * (Bden * Eplus * S))
      hquot_eq.symm
      hmul_bound)⟩

/-- Inline form of the quotient algebra for the left-boundary two-Gamma expression. -/
theorem inline_twoGammaQuotient_sqrt_growth_bound_of_unfolded
    (hunfolded :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
            A * Real.sqrt (1 + ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match hunfolded with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht =>
        Eq.subst
          (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
          (norm_inline_twoGammaQuotient_eq_norm_unfoldedGammaℝLeftBoundaryRatioRealParam t)
          (hbound t ht)⟩

/-- Vertical Stirling quotient corollary for the completed real-Gamma boundary
ratio.

This is the canonical quotient consequence of the two-sided vertical Stirling
formula, specialized to `(1 - it) / 2` and `it / 2`; cf. DLMF §5.11. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_twoGammaQuotient_sqrt_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact inline_twoGammaQuotient_sqrt_growth_bound_of_unfolded
    (unfoldedGammaℝLeftBoundaryRatioRealParam_sqrt_growth_bound_of_numerator_and_denominator
      (twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound hbranch)
      (twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound hbranch))

/-- The historical owner-root spelling for the left-boundary two-Gamma quotient estimate.

The proof is only name transport from the canonical two-sided vertical `Complex.Gamma`
Stirling quotient primitive. -/
theorem verticalStirling_complexGamma_leftBoundary_twoGammaQuotient_sqrt_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact
    twoSidedVerticalComplexGammaStirling_leftBoundary_twoGammaQuotient_sqrt_growth_bound hbranch

/-- Classical two-sided vertical Stirling control for the inline two-Gamma quotient on
the left boundary.

This is the smallest special-function input for the left-edge Gamma-ratio: after
substituting `z = it`, apply the two-sided vertical Stirling formula to the numerator
and denominator Gamma factors; cf. DLMF §5.11. -/
theorem classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact
    verticalStirling_complexGamma_leftBoundary_twoGammaQuotient_sqrt_growth_bound hbranch

/-- Classical two-sided vertical Stirling control for the unfolded completed real-Gamma
ratio on the left boundary.

This is now only transport from the inline two-Gamma quotient to the local unfolded
ratio name. -/
theorem classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match
    classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling
      hbranch
    with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht =>
        calc
          ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ =
              ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
                    Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
                  (π ^ (-((t : ℂ) * Complex.I) / 2) *
                    Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ :=
            (congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t)).symm
          _ ≤ A * Real.sqrt (1 + ‖t‖) :=
            hbound t ht⟩

end
end LFunctions
end Boundary
