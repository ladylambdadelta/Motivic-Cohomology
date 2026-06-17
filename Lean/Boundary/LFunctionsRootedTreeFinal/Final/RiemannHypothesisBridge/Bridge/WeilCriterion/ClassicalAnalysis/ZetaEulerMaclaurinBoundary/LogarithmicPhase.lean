import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.RealPhaseBasics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.DyadicComparison
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Angle
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

/-- Arithmetic normalization for scaling an `8`-constant estimate by `5/2`. -/
theorem Real.five_div_two_mul_eight_eq_twenty_for_logarithmicPhase :
    (5 / 2 : ℝ) * 8 = 20 := by
  have hfive_mul_eight_nat : (5 * 8 : ℕ) = 40 :=
    rfl
  have htwenty_mul_two_nat : (20 * 2 : ℕ) = 40 :=
    rfl
  have hfive_mul_eight :
      (5 : ℝ) * 8 = 40 :=
    Eq.trans
      (Nat.cast_mul 5 8).symm
      (congrArg (fun n : ℕ => (n : ℝ)) hfive_mul_eight_nat)
  have htwenty_mul_two :
      (20 : ℝ) * 2 = 40 :=
    Eq.trans
      (Nat.cast_mul 20 2).symm
      (congrArg (fun n : ℕ => (n : ℝ)) htwenty_mul_two_nat)
  have hmul :
      (5 : ℝ) * 8 = 20 * 2 :=
    Eq.trans hfive_mul_eight htwenty_mul_two.symm
  calc
    (5 / 2 : ℝ) * 8 = (5 * 8 : ℝ) / 2 :=
      div_mul_eq_mul_div 5 2 8
    _ = 20 :=
      div_eq_of_eq_mul (show (2 : ℝ) ≠ 0 from two_ne_zero) hmul

/-- Arithmetic normalization for scaling a `16`-constant estimate by `5/2`. -/
theorem Real.five_div_two_mul_sixteen_eq_forty_for_logarithmicPhase :
    (5 / 2 : ℝ) * 16 = 40 := by
  have hfive_mul_sixteen_nat : (5 * 16 : ℕ) = 80 :=
    rfl
  have hforty_mul_two_nat : (40 * 2 : ℕ) = 80 :=
    rfl
  have hfive_mul_sixteen :
      (5 : ℝ) * 16 = 80 :=
    Eq.trans
      (Nat.cast_mul 5 16).symm
      (congrArg (fun n : ℕ => (n : ℝ)) hfive_mul_sixteen_nat)
  have hforty_mul_two :
      (40 : ℝ) * 2 = 80 :=
    Eq.trans
      (Nat.cast_mul 40 2).symm
      (congrArg (fun n : ℕ => (n : ℝ)) hforty_mul_two_nat)
  have hmul :
      (5 : ℝ) * 16 = 40 * 2 :=
    Eq.trans hfive_mul_sixteen hforty_mul_two.symm
  calc
    (5 / 2 : ℝ) * 16 = (5 * 16 : ℝ) / 2 :=
      div_mul_eq_mul_div 5 2 16
    _ = 40 :=
      div_eq_of_eq_mul (show (2 : ℝ) ≠ 0 from two_ne_zero) hmul

/-- The dyadic-cover expression comparison with the `20` block constant. -/
theorem Complex.logarithmicPhase_dyadic_cover_expression_twenty_le_standard
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ) :
    20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) ≤
      40 *
        (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + N) := by
  have hbase :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) ≤
        16 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N) :=
    Complex.logarithmicPhase_dyadic_cover_expression_le_standard t ht N
  have hscale_nonneg : 0 ≤ (5 / 2 : ℝ) :=
    div_nonneg (Nat.cast_nonneg 5) zero_lt_two.le
  have hscaled :
      (5 / 2 : ℝ) *
          (8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1)) ≤
        (5 / 2 : ℝ) *
          (16 *
            (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
              Real.log (2 + N)) :=
    mul_le_mul_of_nonneg_left hbase hscale_nonneg
  have hleft :
      (5 / 2 : ℝ) *
          (8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1)) =
        20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) := by
    calc
      (5 / 2 : ℝ) *
          (8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1)) =
          ((5 / 2 : ℝ) * 8) *
            (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) :=
        (mul_assoc (5 / 2 : ℝ) 8
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1)).symm
      _ = 20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) :=
        congrArg
          (fun c : ℝ =>
            c * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1))
          Real.five_div_two_mul_eight_eq_twenty_for_logarithmicPhase
  have hright :
      (5 / 2 : ℝ) *
          (16 *
            (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
              Real.log (2 + N)) =
        40 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N) := by
    calc
      (5 / 2 : ℝ) *
          (16 *
            (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
              Real.log (2 + N)) =
          ((5 / 2 : ℝ) * 16) *
            (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
              Real.log (2 + N) := by
        calc
          (5 / 2 : ℝ) *
              (16 *
                (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                  Real.log (2 + N)) =
              ((5 / 2 : ℝ) *
                (16 *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) *
                    Real.log (2 + N) :=
            (mul_assoc (5 / 2 : ℝ)
              (16 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))
              (Real.log (2 + N))).symm
          _ =
              (((5 / 2 : ℝ) * 16) *
                (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) *
                  Real.log (2 + N) := by
            exact congrArg
              (fun r : ℝ => r * Real.log (2 + N))
              ((mul_assoc (5 / 2 : ℝ) 16
                (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))).symm)
      _ =
          40 *
            (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
              Real.log (2 + N) :=
        congrArg
          (fun c : ℝ =>
            c * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
              Real.log (2 + N))
          Real.five_div_two_mul_sixteen_eq_forty_for_logarithmicPhase
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤
        40 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N))
    hleft
    (Eq.subst
      (motive := fun right : ℝ =>
        (5 / 2 : ℝ) *
            (8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1)) ≤
          right)
      hright
      hscaled)
/-- Dyadic summation primitive that turns the one-block first-derivative
estimate into the global logarithmic-phase partial-sum estimate. -/
theorem Complex.logarithmicPhase_dyadic_decomposition_bound_of_block
    (hblock :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                ‖∑ n ∈ Finset.Icc a b,
                  ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                  20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1)) :
    ∀ t : ℝ,
      1 ≤ ‖t‖ →
        ∀ N : ℕ,
          ‖∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
              40 *
                (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                  Real.log (2 + N) := by
  intro t ht N
  have hcover :
      ‖∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          20 *
            (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) :=
    Complex.logarithmicPhase_dyadic_block_cover_bound hblock t ht N
  have hcomparison :
      20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) ≤
        40 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N) :=
    Complex.logarithmicPhase_dyadic_cover_expression_twenty_le_standard t ht N
  exact le_trans hcover hcomparison

/-- Dyadic decomposition form of the first-derivative estimate for the
logarithmic phase. -/
theorem Complex.logarithmicPhase_dyadic_firstDerivative_sum_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hfiniteDifference :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                Complex.realPhase_integerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_reducedIntegerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_integerIncrementSeparatedOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                  (‖t‖ / ((b + 1 : ℕ) : ℝ)))
    (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        40 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N) := by
  exact
    Complex.logarithmicPhase_dyadic_decomposition_bound_of_block
      (fun t ht {a} {b} ha hab =>
        let hfd := hfiniteDifference t ht ha hab
        Complex.logarithmicPhase_monotone_firstDerivative_block_bound
          t ht ha hab hfd.1 hfd.2.1 hfd.2.2)
      t ht N

/-- Classical first-derivative estimate for the concrete logarithmic phase
`x ↦ exp(-it log x)` after the required finite-difference arithmetic is
available.

This is the remaining van der Corput/first-derivative-test input after the
phase derivative and derivative norm have been computed from the definition. -/
theorem Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_of_finiteDifference
    (hfiniteDifference :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                Complex.realPhase_integerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_reducedIntegerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_integerIncrementSeparatedOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                  (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  have hA_pos : 0 < (40 : ℝ) :=
    Nat.cast_pos.mpr
      (show (0 : ℕ) < 40 from Nat.succ_pos 39)
  have hA_bound :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                (40 : ℝ) *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) :=
    fun t ht N =>
      Complex.logarithmicPhase_dyadic_firstDerivative_sum_bound
        t ht hfiniteDifference N
  exact Exists.intro (40 : ℝ) (And.intro hA_pos hA_bound)

/-- The first-derivative-test root after the concrete derivative and derivative
norm have been isolated. -/
theorem Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_of_derivative_control
    (_hderiv :
      ∀ t : ℝ, ∀ {x : ℝ}, 0 < x →
        deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x =
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x))
    (_hderiv_norm :
      ∀ t : ℝ, ∀ {x : ℝ}, 0 < x →
        ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
          ‖t‖ / x)
    (hfiniteDifference :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                Complex.realPhase_integerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_reducedIntegerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_integerIncrementSeparatedOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                  (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  exact
    Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_of_finiteDifference
      hfiniteDifference

/-- The standard first-derivative-test owner root for the concrete logarithmic
phase.  This is the analytic input behind the Euler-Maclaurin boundary
package; cf. Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound
    (hfiniteDifference :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                Complex.realPhase_integerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_reducedIntegerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_integerIncrementSeparatedOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                  (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  exact
    Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_of_derivative_control
      (fun t {x} hx =>
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq t hx)
      (fun t {x} hx =>
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq t hx)
      hfiniteDifference

/-- First-derivative estimate for the logarithmic phase sums on the boundary
line.

The previous scaffold stated an `O(log N)` bound for the unweighted sums
`∑ n^{-it}`.  The owner-level first-derivative estimate has the standard
oscillatory-sum size shown here; the reciprocal Abel weight is introduced in
`AbelTail`. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_bound :
    (∀ t : ℝ,
      1 ≤ ‖t‖ →
        ∀ {a b : ℕ},
          1 ≤ a →
            a ≤ b →
              Complex.realPhase_integerIncrementMonotoneOn
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
              Complex.realPhase_reducedIntegerIncrementMonotoneOn
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
              Complex.realPhase_integerIncrementSeparatedOn
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                (‖t‖ / ((b + 1 : ℕ) : ℝ))) →
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  intro hfiniteDifference
  exact
    Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound
      hfiniteDifference

end

end LFunctions
end Boundary
