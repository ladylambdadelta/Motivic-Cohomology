import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.DerivativeOscillatoryKernel.Owner

/-!
# Paley-Wiener low-frequency decay weights

This file owns the elementary real decay-weight arithmetic and the low-frequency
Fourier decay estimate for the first derivative-source oscillatory integral.
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

/-- The deterministic zero-order Fourier constant for the first derivative source. -/
noncomputable def zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) : ℝ :=
  zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b 1 *
    zetaPaleyWienerSupportIntervalLength I + 1

/-- The deterministic zero-order Fourier constant is positive. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant_pos
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    0 <
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant
        f I a b :=
  let C0 : ℝ := zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b 1
  let hC0pos : 0 < C0 :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_pos f I a b 1
  let hC0_nonneg : 0 ≤ C0 :=
    le_of_lt hC0pos
  let hraw_nonneg : 0 ≤ C0 * zetaPaleyWienerSupportIntervalLength I :=
    mul_nonneg hC0_nonneg (zetaPaleyWienerSupportIntervalLength_nonnegative I)
  lt_of_le_of_lt hraw_nonneg
    (lt_add_of_pos_right
      (C0 * zetaPaleyWienerSupportIntervalLength I)
      zero_lt_one)

/-- The deterministic zero-order Fourier constant bounds the first derivative
source oscillatory integral. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b x y : ℝ)
    (hxLeft : a ≤ x) (hxRight : x ≤ b) :
    ‖∫ t : ℝ,
      zetaPaleyWienerVerticalLineIBPDerivative f x t *
        zetaPaleyWienerVerticalOscillation y t‖ ≤
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant
        f I a b :=
  let C0 : ℝ := zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b 1
  let hC0pos : 0 < C0 :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_pos f I a b 1
  let hC0_nonneg : 0 ≤ C0 :=
    le_of_lt hC0pos
  let hC0bound :
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C0 :=
    fun x hxLeftLocal hxRightLocal t =>
      match zetaPaleyWienerSupportInterval_inside_or_outside I t with
      | Or.inl hinside =>
          let hjet :
              ‖zetaPaleyWienerHorizontalTwistVerticalJet f 1 x t‖ ≤ C0 :=
            zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_bound
              f I a b 1 (x, t) ⟨⟨hxLeftLocal, hxRightLocal⟩, hinside⟩
          let hiterated :
              ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t‖ ≤ C0 :=
            Eq.subst
              (motive := fun v : ℂ => ‖v‖ ≤ C0)
              (zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet
                f 1 x t).symm
              hjet
          Eq.subst
            (motive := fun v : ℂ => ‖v‖ ≤ C0)
            (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)
            hiterated
      | Or.inr houtside =>
          match houtside with
          | Or.inl hbelow =>
              let hzero :
                  zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t = 0 :=
                zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_off_supportInterval
                  f I 1 x t hbelow
              let hiterated :
                  ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t‖ ≤ C0 :=
                Eq.subst
                  (motive := fun v : ℂ => ‖v‖ ≤ C0)
                  hzero.symm
                  (complex_norm_zero_le_of_pos C0 hC0pos)
              Eq.subst
                (motive := fun v : ℂ => ‖v‖ ≤ C0)
                (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)
                hiterated
          | Or.inr habove =>
              let hzero :
                  zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t = 0 :=
                zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
                  f I 1 x t habove
              let hiterated :
                  ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t‖ ≤ C0 :=
                Eq.subst
                  (motive := fun v : ℂ => ‖v‖ ≤ C0)
                  hzero.symm
                  (complex_norm_zero_le_of_pos C0 hC0pos)
              Eq.subst
                (motive := fun v : ℂ => ‖v‖ ≤ C0)
                (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)
                hiterated
  zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_le_bumpedBound
    f I a b C0 hC0_nonneg hC0bound x y hxLeft hxRight

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
  let C : ℝ :=
    zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant
      f I a b
  exact ⟨C,
    zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant_pos
      f I a b,
    fun x y hxLeft hxRight =>
    let hweight :
      C * (1 + ‖y‖) ^ (-(0 : ℤ)) = C := by
      exact Eq.trans
        (congrArg (fun v : ℝ => C * v) (zetaPaleyWiener_zeroDecayWeight y))
        (mul_one C)
    Eq.subst
      (motive := fun v : ℝ =>
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖ ≤ v)
      hweight.symm
      (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant_bound
        f I a b x y hxLeft hxRight)⟩

/-- The deterministic low-frequency positive-order Fourier constant for the first
derivative source. -/
noncomputable def zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) : ℝ :=
  zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant f I a b *
    (2 : ℝ) ^ (Nat.succ N)

/-- The deterministic low-frequency positive-order Fourier constant is positive. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant_pos
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    0 <
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant
        f I a b N :=
  mul_pos
    (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant_pos
      f I a b)
    (pow_pos zero_lt_two (Nat.succ N))

/-- The deterministic low-frequency positive-order Fourier constant gives the
renormalized low-frequency decay bound. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      ‖y‖ ≤ 1 →
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖
        ≤
          zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant
              f I a b N *
            (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
  fun x y hxLeft hxRight hy =>
    let C0 : ℝ :=
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant
        f I a b
    let hC0pos : 0 < C0 :=
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant_pos
        f I a b
    let hzero :
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖ ≤ C0 :=
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant_bound
        f I a b x y hxLeft hxRight
    let habsorb :
        C0 ≤
          (C0 * (2 : ℝ) ^ (Nat.succ N)) *
            (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
      zetaPaleyWiener_lowFrequency_decayWeight_absorbs_constant
        C0 (le_of_lt hC0pos) N hy
    le_trans hzero habsorb

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
  exact
    ⟨zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant
        f I a b N,
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant_pos
        f I a b N,
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant_bound
        f I a b N⟩

end LFunctions
end Boundary
