import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.DerivativeOscillatoryKernel.Owner

/-!
# Paley-Wiener low-frequency decay weights

This file owns the elementary real decay-weight arithmetic and the low-frequency
Fourier decay estimate for the first derivative-source oscillatory integral. It
is copy-first extracted from the current Paley-Wiener owner file and is not
imported by that parent yet, so declaration names intentionally match the
existing owner surface.
-/

open scoped Real
open MeasureTheory

namespace Boundary
namespace LFunctions

open ZetaAdmissibleFunction

/-- The zeroth vertical-frequency decay weight is one. -/
theorem zetaPaleyWiener_zeroDecayWeight
    (y : ℝ) :
    (1 + ‖y‖) ^ (-(0 : ℤ)) = (1 : ℝ) := by
  exact zpow_zero (1 + ‖y‖)

/-- The real vertical-frequency decay weight is nonnegative. -/
theorem zetaPaleyWiener_realVerticalDecayWeight_nonnegative
    (y : ℝ) (N : ℕ) :
    0 ≤ (1 + ‖y‖) ^ (-(N : ℤ)) := by
  exact zpow_nonneg
    (add_nonneg zero_le_one (norm_nonneg y))
    (-(N : ℤ))

/-- Low vertical frequency bounds the real decay base by `2`. -/
theorem zetaPaleyWiener_lowFrequency_realDecayBase_le_two
    {y : ℝ} (hy : ‖y‖ ≤ 1) :
    1 + ‖y‖ ≤ (2 : ℝ) := by
  exact Eq.subst
    (motive := fun v : ℝ => 1 + ‖y‖ ≤ v)
    one_add_one_eq_two
    (add_le_add_left hy 1)

/-- The real vertical-frequency decay base is positive. -/
theorem zetaPaleyWiener_realDecayBase_pos
    (y : ℝ) :
    0 < 1 + ‖y‖ :=
  lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right (norm_nonneg y))

/-- The real vertical-frequency decay base is nonzero. -/
theorem zetaPaleyWiener_realDecayBase_ne_zero
    (y : ℝ) :
    1 + ‖y‖ ≠ 0 :=
  ne_of_gt (zetaPaleyWiener_realDecayBase_pos y)

/-- Low vertical frequency bounds every natural power of the real decay base by the
corresponding power of `2`. -/
theorem zetaPaleyWiener_lowFrequency_realDecayBase_pow_le_two_pow
    (m : ℕ) {y : ℝ} (hy : ‖y‖ ≤ 1) :
    (1 + ‖y‖) ^ m ≤ (2 : ℝ) ^ m := by
  exact pow_le_pow_left₀
    (add_nonneg zero_le_one (norm_nonneg y))
    (zetaPaleyWiener_lowFrequency_realDecayBase_le_two hy)
    m

/-- A positive base whose `m`th power is bounded by `A` has reciprocal `m`th z-power
absorbing `A`. -/
theorem zetaPaleyWiener_pow_bound_mul_negative_zpow_ge_one
    (A X : ℝ) (m : ℕ)
    (hX_pos : 0 < X)
    (hpow : X ^ m ≤ A) :
    1 ≤ A * X ^ (-(m : ℤ)) := by
  have hXpow_pos : 0 < X ^ m :=
    pow_pos hX_pos m
  have hdiv :
      1 ≤ A / X ^ m := by
    have hone_mul :
        1 * X ^ m = X ^ m :=
      one_mul (X ^ m)
    exact (le_div_iff₀ hXpow_pos).mpr
      (Eq.subst
        (motive := fun v : ℝ => v ≤ A)
        hone_mul.symm
        hpow)
  have hnegative :
      X ^ (-(m : ℤ)) = (X ^ m)⁻¹ :=
    zpow_neg X m
  have hproduct :
      A * X ^ (-(m : ℤ)) = A / X ^ m :=
    Eq.trans
      (congrArg (fun v : ℝ => A * v) hnegative)
      (div_eq_mul_inv A (X ^ m)).symm
  exact Eq.subst
    (motive := fun v : ℝ => 1 ≤ v)
    hproduct.symm
    hdiv

/-- The low-frequency reciprocal decay weight absorbs the `2 ^ m` renormalization. -/
theorem zetaPaleyWiener_lowFrequency_two_pow_mul_negative_zpow_ge_one
    (m : ℕ) {y : ℝ} (hy : ‖y‖ ≤ 1) :
    1 ≤ (2 : ℝ) ^ m * (1 + ‖y‖) ^ (-(m : ℤ)) := by
  exact zetaPaleyWiener_pow_bound_mul_negative_zpow_ge_one
    ((2 : ℝ) ^ m)
    (1 + ‖y‖)
    m
    (zetaPaleyWiener_realDecayBase_pos y)
    (zetaPaleyWiener_lowFrequency_realDecayBase_pow_le_two_pow m hy)

/-- The positive-order low-frequency decay weight absorbs one bounded constant after
renormalization by `2 ^ (N + 1)`. -/
theorem zetaPaleyWiener_lowFrequency_decayWeight_absorbs_unit
    (N : ℕ) {y : ℝ} (hy : ‖y‖ ≤ 1) :
    1 ≤ (2 : ℝ) ^ (Nat.succ N) *
        (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  exact zetaPaleyWiener_lowFrequency_two_pow_mul_negative_zpow_ge_one
    (Nat.succ N) hy

/-- A positive constant is absorbed by the low-frequency positive-order decay weight after
renormalization by `2 ^ (N + 1)`. -/
theorem zetaPaleyWiener_lowFrequency_decayWeight_absorbs_constant
    (C0 : ℝ) (hC0_nonneg : 0 ≤ C0) (N : ℕ) {y : ℝ} (hy : ‖y‖ ≤ 1) :
    C0 ≤
      (C0 * (2 : ℝ) ^ (Nat.succ N)) *
        (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  have hunit :
      1 ≤ (2 : ℝ) ^ (Nat.succ N) *
          (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    zetaPaleyWiener_lowFrequency_decayWeight_absorbs_unit N hy
  have hscaled :
      C0 * 1 ≤
        C0 *
          ((2 : ℝ) ^ (Nat.succ N) *
            (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) :=
    mul_le_mul_of_nonneg_left hunit hC0_nonneg
  have hleft :
      C0 * 1 = C0 :=
    mul_one C0
  have hright :
      C0 *
          ((2 : ℝ) ^ (Nat.succ N) *
            (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) =
        (C0 * (2 : ℝ) ^ (Nat.succ N)) *
          (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
    exact (mul_assoc C0 ((2 : ℝ) ^ (Nat.succ N))
      ((1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))).symm
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤
        (C0 * (2 : ℝ) ^ (Nat.succ N)) *
          (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
    hleft
    (Eq.subst
      (motive := fun v : ℝ => C0 * 1 ≤ v)
      hright
      hscaled)

/-- Zero-order Fourier decay for the compactly supported horizontal-twist derivative
family. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformDecay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-(0 : ℤ)) := by
  rcases zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformBound
      f I a b with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x y hx_left hx_right
  have hweight :
      C * (1 + ‖y‖) ^ (-(0 : ℤ)) = C := by
    exact Eq.trans
      (congrArg (fun v : ℝ => C * v) (zetaPaleyWiener_zeroDecayWeight y))
      (mul_one C)
  exact Eq.subst
    (motive := fun v : ℝ =>
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤ v)
    hweight.symm
    (hCbound x y hx_left hx_right)

/-- Low-frequency positive-order Fourier decay follows from the zero-order bound after
renormalizing the constant on `|y| ≤ 1`. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_lowFrequency
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖y‖ ≤ 1 →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  rcases zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformBound
      f I a b with ⟨C0, hC0pos, hC0bound⟩
  refine ⟨C0 * (2 : ℝ) ^ (Nat.succ N),
    mul_pos hC0pos (pow_pos zero_lt_two (Nat.succ N)), ?_⟩
  intro x y hx_left hx_right hy
  have hzero :
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤ C0 :=
    hC0bound x y hx_left hx_right
  have habsorb :
      C0 ≤
        (C0 * (2 : ℝ) ^ (Nat.succ N)) *
          (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    zetaPaleyWiener_lowFrequency_decayWeight_absorbs_constant
      C0 (le_of_lt hC0pos) N hy
  exact le_trans hzero habsorb

end LFunctions
end Boundary
