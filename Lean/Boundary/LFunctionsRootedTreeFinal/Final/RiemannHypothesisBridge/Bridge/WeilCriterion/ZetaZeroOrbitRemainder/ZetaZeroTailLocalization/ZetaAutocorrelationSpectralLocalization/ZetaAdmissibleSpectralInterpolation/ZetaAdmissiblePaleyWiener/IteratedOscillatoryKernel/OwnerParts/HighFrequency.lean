import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.LowFrequencyDecay.Owner

/-!
# Paley-Wiener iterated oscillatory kernels

This file owns the arbitrary iterated-derivative oscillatory kernels and the
high-frequency repeated-integration-by-parts estimates used by the
Paley-Wiener owner.
-/

open scoped Real
open MeasureTheory
open scoped ContDiff

namespace Boundary
namespace LFunctions

open ZetaAdmissibleFunction

/-- The arbitrary iterated-derivative oscillatory kernel is integrable. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y : ℝ) :
    Integrable
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t) := by
  exact (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_continuous
    f n x y).integrable_of_hasCompactSupport
      (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_hasCompactSupport f n x y)

/-- The deterministic zero-order constant for arbitrary iterated oscillatory integrals. -/
noncomputable def zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start : ℕ) : ℝ :=
  zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b start *
    zetaPaleyWienerSupportIntervalLength I + 1

/-- The deterministic zero-order iterated oscillatory constant is positive. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant_pos
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start : ℕ) :
    0 <
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant
        f I a b start :=
  let C0 : ℝ :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b start
  let hC0pos : 0 < C0 :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_pos f I a b start
  let hC0_nonneg : 0 ≤ C0 :=
    le_of_lt hC0pos
  let hraw_nonneg : 0 ≤ C0 * zetaPaleyWienerSupportIntervalLength I :=
    mul_nonneg hC0_nonneg (zetaPaleyWienerSupportIntervalLength_nonnegative I)
  lt_of_le_of_lt hraw_nonneg
    (lt_add_of_pos_right
      (C0 * zetaPaleyWienerSupportIntervalLength I)
      zero_lt_one)

/-- The deterministic zero-order constant bounds arbitrary iterated oscillatory integrals. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start : ℕ) (x y : ℝ)
    (hxLeft : a ≤ x) (hxRight : x ≤ b) :
    ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant
        f I a b start :=
  let C0 : ℝ :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b start
  let hC0pos : 0 < C0 :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_pos f I a b start
  let hC0_nonneg : 0 ≤ C0 :=
    le_of_lt hC0pos
  let hsourceBound : ∀ t : ℝ,
      t ∈ tsupport f.toZetaTestFunction →
      ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t‖ ≤ C0 :=
    fun t ht =>
      let hinside : I.lower ≤ t ∧ t ≤ I.upper :=
        ⟨I.lower_mem t ht, I.upper_mem t ht⟩
      let hjet :
          ‖zetaPaleyWienerHorizontalTwistVerticalJet f start x t‖ ≤ C0 :=
        zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_bound
          f I a b start (x, t) ⟨⟨hxLeft, hxRight⟩, hinside⟩
      Eq.subst
        (motive := fun v : ℂ => ‖v‖ ≤ C0)
        (zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet
          f start x t).symm
        hjet
  let hraw :
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤
        C0 * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_intervalLength_mul_bound
      f I start x y C0 hC0_nonneg
      (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable f start x y)
      hsourceBound
  let hle :
      C0 * zetaPaleyWienerSupportIntervalLength I ≤
        C0 * zetaPaleyWienerSupportIntervalLength I + 1 :=
    le_add_of_nonneg_right zero_le_one
  le_trans hraw hle

/-- The deterministic zero-order constant bounds arbitrary iterated oscillatory integrals
with the zeroth decay weight. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant_decay_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start : ℕ) (x y : ℝ)
    (hxLeft : a ≤ x) (hxRight : x ≤ b) (hyHigh : 1 ≤ ‖y‖) :
    ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant
        f I a b start * (1 + ‖y‖) ^ (-(0 : ℤ)) :=
  let C : ℝ :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant
      f I a b start
  let hbase_ge_two : (2 : ℝ) ≤ 1 + ‖y‖ :=
    Eq.subst
      (motive := fun v : ℝ => v ≤ 1 + ‖y‖)
      one_add_one_eq_two
      (add_le_add_left hyHigh 1)
  let hbase_pos : 0 < 1 + ‖y‖ :=
    lt_of_lt_of_le zero_lt_two hbase_ge_two
  let hbase_ne_zero : 1 + ‖y‖ ≠ 0 :=
    ne_of_gt hbase_pos
  let hbound :
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤ C :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant_bound
      f I a b start x y hxLeft hxRight
  let hweightEq : C * (1 + ‖y‖) ^ (-(0 : ℤ)) = C :=
    Eq.trans
      (congrArg (fun v : ℝ => C * v) (zetaPaleyWiener_zeroDecayWeight y))
      (mul_one C)
  Eq.subst
    (motive := fun v : ℝ =>
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤ v)
    hweightEq.symm
    hbound

/-- Zero-order high-frequency decay for arbitrary iterated derivative oscillatory integrals
is just the compact-support bound, since the zeroth decay weight is one. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_zeroOrder_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖
          ≤ C * (1 + ‖y‖) ^ (-(0 : ℤ)) := by
  let C : ℝ :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant
      f I a b start
  exact ⟨C,
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant_pos
      f I a b start,
    fun x y hxLeft hxRight highFrequency =>
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant_decay_bound
        f I a b start x y hxLeft hxRight highFrequency⟩

/-- The arbitrary iterated horizontal-twist derivative source is smooth. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_contDiff
    (f : ZetaAdmissibleFunction) (start : ℕ) (x : ℝ) :
    ContDiff ℝ ∞
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t) := by
  have hjet_plane :
      ContDiff ℝ ∞
        (fun p : ℝ × ℝ =>
          zetaPaleyWienerHorizontalTwistVerticalJet f start p.1 p.2) :=
    zetaPaleyWienerHorizontalTwistVerticalJet_contDiff f start
  have hline :
      ContDiff ℝ ∞ (fun t : ℝ => (x, t)) :=
    contDiff_const.prod contDiff_id
  have hjet_line :
      ContDiff ℝ ∞
        (fun t : ℝ => zetaPaleyWienerHorizontalTwistVerticalJet f start x t) :=
    hjet_plane.comp hline
  have hfun_eq : ∀ t : ℝ,
      zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t =
        zetaPaleyWienerHorizontalTwistVerticalJet f start x t :=
    fun t : ℝ =>
      zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet f start x t
  have hfun :
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t) =
        fun t : ℝ => zetaPaleyWienerHorizontalTwistVerticalJet f start x t :=
    funext hfun_eq
  exact Eq.subst
    (motive := fun g : ℝ → ℂ => ContDiff ℝ ∞ g)
    hfun.symm
    hjet_line

/-- The arbitrary iterated horizontal-twist derivative source is differentiable. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_differentiableAt
    (f : ZetaAdmissibleFunction) (start : ℕ) (x t : ℝ) :
    DifferentiableAt ℝ
      (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
      t := by
  have horder : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
    WithTop.coe_le_coe.2 (show (1 : ℕ∞) ≤ ⊤ from le_top)
  exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_contDiff
    f start x).differentiable horder t

/-- The derivative value of the `start`th iterated source is the successor iterated source. -/
theorem deriv_zetaPaleyWienerHorizontalTwistIteratedDerivative
    (f : ZetaAdmissibleFunction) (start : ℕ) (x t : ℝ) :
    deriv
      (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
      t =
      zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t := by
  exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_succ f start x t).symm

/-- The derivative of the `start`th iterated source is the successor iterated source. -/
theorem hasDerivAt_zetaPaleyWienerHorizontalTwistIteratedDerivative
    (f : ZetaAdmissibleFunction) (start : ℕ) (x t : ℝ) :
    HasDerivAt
      (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
      (zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t)
      t := by
  have hderiv :
      HasDerivAt
        (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
        (deriv
          (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
          t)
        t :=
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_differentiableAt
      f start x t).hasDerivAt
  exact Eq.subst
    (motive := fun v : ℂ =>
      HasDerivAt
        (fun u : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x u)
        v
        t)
    (deriv_zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t)
    hderiv

/-- The boundary term for arbitrary iterated derivative oscillatory integration by parts
vanishes at strict cutoffs outside the certified support interval. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_boundaryTerm_eq_zero
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (start : ℕ) (x y lower upper : ℝ)
    (hlower : lower < I.lower) (hupper : I.upper < upper) :
    zetaPaleyWienerHorizontalTwistIteratedDerivative f start x upper *
        zetaPaleyWienerVerticalOscillation y upper -
      zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
        zetaPaleyWienerVerticalOscillation y lower =
      0 := by
  have hupper_zero :
      zetaPaleyWienerHorizontalTwistIteratedDerivative f start x upper = 0 :=
    zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
      f I start x upper hupper
  have hlower_zero :
      zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower = 0 :=
    zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_off_supportInterval
      f I start x lower hlower
  calc
    zetaPaleyWienerHorizontalTwistIteratedDerivative f start x upper *
          zetaPaleyWienerVerticalOscillation y upper -
        zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
          zetaPaleyWienerVerticalOscillation y lower
        = 0 * zetaPaleyWienerVerticalOscillation y upper -
            zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
              zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ =>
              v * zetaPaleyWienerVerticalOscillation y upper -
                zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
                  zetaPaleyWienerVerticalOscillation y lower)
            hupper_zero
    _ = 0 - zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
            zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ =>
              v - zetaPaleyWienerHorizontalTwistIteratedDerivative f start x lower *
                zetaPaleyWienerVerticalOscillation y lower)
            (zero_mul (zetaPaleyWienerVerticalOscillation y upper))
    _ = 0 - 0 * zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ => 0 - v * zetaPaleyWienerVerticalOscillation y lower)
            hlower_zero
    _ = 0 - 0 := by
          exact congrArg
            (fun v : ℂ => 0 - v)
            (zero_mul (zetaPaleyWienerVerticalOscillation y lower))
    _ = 0 := sub_zero (0 : ℂ)

/-- The frequency-multiplied oscillatory kernel for an iterated source is integrable. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_frequency_integrable
    (f : ZetaAdmissibleFunction) (start : ℕ) (x y : ℝ) :
    Integrable
      (fun t : ℝ =>
        zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
          ((Complex.I * (y : ℂ)) *
            zetaPaleyWienerVerticalOscillation y t)) := by
  have hcontinuous :
      Continuous
        (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
            ((Complex.I * (y : ℂ)) *
              zetaPaleyWienerVerticalOscillation y t)) := by
    exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_continuous f start x).mul
      (continuous_const.mul
        (Complex.continuous_exp.comp
          ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal)))
  have hsupport :
      HasCompactSupport
        (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
            ((Complex.I * (y : ℂ)) *
              zetaPaleyWienerVerticalOscillation y t)) := by
    exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_hasCompactSupport
      f start x).mul_right
  exact hcontinuous.integrable_of_hasCompactSupport hsupport

/-- The product-rule integration-by-parts identity for the `start`th iterated source. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_integral_mul_frequency_eq_neg_succ
    (f : ZetaAdmissibleFunction) (start : ℕ) (x y : ℝ) :
    (∫ t : ℝ,
        zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
          (Complex.I * (y : ℂ) * zetaPaleyWienerVerticalOscillation y t)) =
      -∫ t : ℝ,
        zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t *
          zetaPaleyWienerVerticalOscillation y t := by
  let A : ℂ := Complex.I * (y : ℂ)
  let H : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t
  let V : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerVerticalOscillation y t
  let D : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t
  have hH :
      ∀ t : ℝ, HasDerivAt H (D t) t := by
    intro t
    exact hasDerivAt_zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t
  have hV :
      ∀ t : ℝ, HasDerivAt V (A * V t) t := by
    intro t
    exact hasDerivAt_zetaPaleyWienerVerticalOscillation y t
  have hHDV :
      Integrable (fun t : ℝ => H t * (A * V t)) := by
    exact zetaPaleyWienerIteratedDerivativeOscillatoryKernel_frequency_integrable
      f start x y
  have hDV :
      Integrable (fun t : ℝ => D t * V t) := by
    exact zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable
      f (start + 1) x y
  have hHV :
      Integrable (fun t : ℝ => H t * V t) := by
    exact zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable
      f start x y
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    hH hV hHDV hDV hHV

/-- Pulling the constant vertical frequency out of the current oscillatory integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_frequency_mul_eq_integral
    (f : ZetaAdmissibleFunction) (start : ℕ) (x y : ℝ) :
    (Complex.I * (y : ℂ)) *
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
      ∫ t : ℝ,
        zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
          (Complex.I * (y : ℂ) * zetaPaleyWienerVerticalOscillation y t) := by
  let A : ℂ := Complex.I * (y : ℂ)
  let H : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t
  let V : ℝ → ℂ :=
    fun t : ℝ => zetaPaleyWienerVerticalOscillation y t
  have hright_integrand :
      (fun t : ℝ => H t * (A * V t)) =
        fun t : ℝ => A * (H t * V t) :=
    funext
      (fun t : ℝ =>
        calc
          H t * (A * V t) = (H t * A) * V t := by
            exact (mul_assoc (H t) A (V t)).symm
          _ = (A * H t) * V t := by
            exact congrArg (fun v : ℂ => v * V t) (mul_comm (H t) A)
          _ = A * (H t * V t) := by
            exact mul_assoc A (H t) (V t))
  have hintegral :
      (∫ t : ℝ, H t * (A * V t)) =
        A * ∫ t : ℝ, H t * V t := by
    exact Eq.trans
      (congrArg
        (fun q : ℝ → ℂ => ∫ t : ℝ, q t)
        hright_integrand)
      (MeasureTheory.integral_mul_left A (fun t : ℝ => H t * V t))
  have hdefs : zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
      ∫ t : ℝ, zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
        zetaPaleyWienerVerticalOscillation y t := by
    rfl
  exact Eq.trans
    (congrArg (fun q : ℂ => A * q) hdefs)
    hintegral.symm

/-- The successor iterated source integral is the successor oscillatory integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_succ_integral_eq
    (f : ZetaAdmissibleFunction) (start : ℕ) (x y : ℝ) :
    (∫ t : ℝ,
        zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t *
          zetaPaleyWienerVerticalOscillation y t) =
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y := by
  rfl

/-- One integration-by-parts identity for arbitrary iterated derivative oscillatory
integrals, before solving for the current integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_mul_frequency_eq_neg_succ
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (start : ℕ) (x y : ℝ) :
    (Complex.I * (y : ℂ)) *
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
      -zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y := by
  have hleft :
      (Complex.I * (y : ℂ)) *
          zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
        ∫ t : ℝ,
          zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
            (Complex.I * (y : ℂ) * zetaPaleyWienerVerticalOscillation y t) :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_frequency_mul_eq_integral
      f start x y
  have hibp :
      (∫ t : ℝ,
          zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
            (Complex.I * (y : ℂ) * zetaPaleyWienerVerticalOscillation y t)) =
        -∫ t : ℝ,
          zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t *
            zetaPaleyWienerVerticalOscillation y t :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_integral_mul_frequency_eq_neg_succ
      f start x y
  have hright :
      (∫ t : ℝ,
          zetaPaleyWienerHorizontalTwistIteratedDerivative f (start + 1) x t *
            zetaPaleyWienerVerticalOscillation y t) =
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_succ_integral_eq
      f start x y
  exact hleft.trans
    (hibp.trans
      (congrArg Neg.neg hright))

/-- Solving the arbitrary iterated integration-by-parts identity for the current integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_eq_I_mul_inverse_mul_succ
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (start : ℕ) (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
      Complex.I * (y : ℂ)⁻¹ *
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y := by
  let K : ℂ := zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y
  let D : ℂ := zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y
  let A : ℂ := Complex.I * (y : ℂ)
  have hA : A ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hy
  have hibp :
      A * K = -D :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_mul_frequency_eq_neg_succ
      f I start x y
  have hcandidate :
      A * (Complex.I * (y : ℂ)⁻¹ * D) = -D :=
    zetaPaleyWiener_frequency_mul_solvedIntegral y hy D
  exact mul_left_cancel₀ hA (hibp.trans hcandidate.symm)

/-- Norm comparison produced by one arbitrary iterated integration-by-parts step. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_inverse_mul_succ
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (start : ℕ) (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤
      ‖(y : ℂ)⁻¹‖ *
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖ := by
  have hidentity :
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
        Complex.I * (y : ℂ)⁻¹ *
          zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_eq_I_mul_inverse_mul_succ
      f I start x y hy
  have hnorm :
      ‖Complex.I * (y : ℂ)⁻¹ *
          zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖ ≤
        ‖(y : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖ :=
    norm_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral_le
      y
      (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y)
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤ ‖(y : ℂ)⁻¹‖ *
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖)
    (congrArg (fun v : ℂ => ‖v‖) hidentity).symm
    hnorm

/-- Real-frequency high-frequency inverse weight comparison for one successor step. -/
theorem zetaPaleyWiener_inverseReal_mul_realWeight_le_successor_highFrequency
    (y : ℝ) (N : ℕ) (hy : 1 ≤ ‖y‖) :
    ‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ)) ≤
      2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  let z : ℂ := (y : ℂ) * Complex.I
  have hz_im :
      z.im = y :=
    paley_ofReal_mul_I_im y
  have hz_norm :
      ‖z.im‖ = ‖y‖ :=
    congrArg (fun v : ℝ => ‖v‖) hz_im
  have hz_high :
      1 ≤ ‖z.im‖ :=
    Eq.subst
      (motive := fun v : ℝ => 1 ≤ v)
      hz_norm.symm
      hy
  have hbase :
      ‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N ≤
        2 * zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaPaleyWiener_inverseIm_mul_weight_le_successor_highFrequency
      z N hz_high
  have hinv :
      ‖(z.im : ℂ)⁻¹‖ = ‖(y : ℂ)⁻¹‖ :=
    congrArg (fun v : ℝ => ‖(v : ℂ)⁻¹‖) hz_im
  have hweightN :
      zetaPaleyWienerVerticalWeight z N =
        (1 + ‖y‖) ^ (-(N : ℤ)) :=
    congrArg (fun v : ℝ => (1 + v) ^ (-(N : ℤ))) hz_norm
  have hweightSucc :
      zetaPaleyWienerVerticalWeight z (N + 1) =
        (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
    have hsucc :
        (-(N + 1 : ℤ)) = -((Nat.succ N : ℕ) : ℤ) :=
      congrArg Neg.neg (Nat.cast_add_one N)
    exact Eq.trans
      (congrArg (fun v : ℝ => (1 + v) ^ (-(N + 1 : ℤ))) hz_norm)
      (congrArg (fun e : ℤ => (1 + ‖y‖) ^ e) hsucc)
  exact Eq.subst
    (motive := fun v : ℝ =>
      v * (1 + ‖y‖) ^ (-(N : ℤ)) ≤
        2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
    hinv
    (Eq.subst
      (motive := fun v : ℝ =>
        ‖(z.im : ℂ)⁻¹‖ * v ≤
          2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
      hweightN
      (Eq.subst
        (motive := fun v : ℝ =>
          ‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N ≤ 2 * v)
        hweightSucc
        hbase))

/-- One high-frequency decay transport step after the arbitrary iterated integration by
parts norm comparison. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_successor_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start N : ℕ)
    (C : ℝ) (hCpos : 0 < C)
    (hnext :
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
          ≤ C * (1 + ‖y‖) ^ (-(N : ℤ))) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      1 ≤ ‖y‖ →
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖
        ≤ (C * 2) * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  intro x y hx_left hx_right hy
  have hy_ne : (y : ℂ) ≠ 0 :=
    zetaPaleyWienerVerticalFrequency_ne_zero_of_high hy
  have hparts :
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤
        ‖(y : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖ :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_inverse_mul_succ
      f I start x y hy_ne
  have hnext_bound :
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
        ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) :=
    hnext x y hx_left hx_right hy
  have hinv_nonneg : 0 ≤ ‖(y : ℂ)⁻¹‖ :=
    norm_nonneg ((y : ℂ)⁻¹)
  have hwith_inv :
      ‖(y : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
        ≤ ‖(y : ℂ)⁻¹‖ *
          (C * (1 + ‖y‖) ^ (-(N : ℤ))) :=
    mul_le_mul_of_nonneg_left hnext_bound hinv_nonneg
  have hC_nonneg : 0 ≤ C :=
    le_of_lt hCpos
  have hweight :
      ‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ)) ≤
        2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    zetaPaleyWiener_inverseReal_mul_realWeight_le_successor_highFrequency
      y N hy
  have hrearrange :
      ‖(y : ℂ)⁻¹‖ * (C * (1 + ‖y‖) ^ (-(N : ℤ))) =
        C * (‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ))) := by
    calc
      ‖(y : ℂ)⁻¹‖ * (C * (1 + ‖y‖) ^ (-(N : ℤ))) =
          (‖(y : ℂ)⁻¹‖ * C) * (1 + ‖y‖) ^ (-(N : ℤ)) := by
        exact (mul_assoc ‖(y : ℂ)⁻¹‖ C ((1 + ‖y‖) ^ (-(N : ℤ)))).symm
      _ = (C * ‖(y : ℂ)⁻¹‖) * (1 + ‖y‖) ^ (-(N : ℤ)) := by
        exact congrArg
          (fun v : ℝ => v * (1 + ‖y‖) ^ (-(N : ℤ)))
          (mul_comm ‖(y : ℂ)⁻¹‖ C)
      _ = C * (‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ))) := by
        exact mul_assoc C ‖(y : ℂ)⁻¹‖ ((1 + ‖y‖) ^ (-(N : ℤ)))
  have hrenorm :
      C * (‖(y : ℂ)⁻¹‖ * (1 + ‖y‖) ^ (-(N : ℤ))) ≤
        C * (2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) :=
    mul_le_mul_of_nonneg_left hweight hC_nonneg
  have htarget :
      C * (2 * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) =
        (C * 2) * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
    exact (mul_assoc C 2 ((1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))).symm
  exact hparts.trans
    (hwith_inv.trans
      (Eq.subst
        (motive := fun v : ℝ =>
          v ≤ (C * 2) * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
        hrearrange.symm
        (hrenorm.trans_eq htarget)))

/-- The deterministic repeated high-frequency constant for arbitrary iterated
oscillatory integrals. -/
noncomputable def zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start N : ℕ) : ℝ :=
  match N with
  | Nat.zero =>
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant
        f I a b start
  | Nat.succ N =>
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
        f I a b (start + 1) N * 2

/-- The deterministic repeated high-frequency constant is positive. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant_pos
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start N : ℕ) :
    0 <
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
        f I a b start N := by
  induction N generalizing start with
  | zero =>
      exact
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant_pos
          f I a b start
  | succ N ih =>
      exact mul_pos (ih (start + 1)) zero_lt_two

/-- The deterministic repeated high-frequency constant bounds arbitrary iterated
oscillatory integrals. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start N : ℕ) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      1 ≤ ‖y‖ →
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖
        ≤ zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
            f I a b start N *
          (1 + ‖y‖) ^ (-(N : ℤ)) := by
  induction N generalizing start with
  | zero =>
      intro x y hxLeft hxRight hyHigh
      exact
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrderConstant_decay_bound
          f I a b start x y hxLeft hxRight hyHigh
  | succ N ih =>
      exact
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_successor_bound
          f I a b start N
          (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
            f I a b (start + 1) N)
          (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant_pos
            f I a b (start + 1) N)
          (ih (start + 1))

/-- High-frequency decay for arbitrary iterated horizontal-twist derivative oscillatory
integrals.  This is the canonical repeated-integration-by-parts statement: starting from
the `start`th derivative source, `N` further integrations by parts give `N` powers of
vertical-frequency decay. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖
          ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) := by
  exact
    ⟨zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
        f I a b start N,
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant_pos
        f I a b start N,
      zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant_bound
        f I a b start N⟩

/-- High-frequency positive-order Fourier decay is the genuine repeated integration by
parts recurrence. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_highFrequency
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  let C : ℝ :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
      f I a b 1 (Nat.succ N)
  exact ⟨C,
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant_pos
      f I a b 1 (Nat.succ N),
    fun x y hx_left hx_right hy =>
      let hiter :
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f 1 x y‖
            ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant_bound
          f I a b 1 (Nat.succ N) x y hx_left hx_right hy
      Eq.subst
        (motive := fun v : ℂ =>
          ‖v‖ ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
        (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_one f x y)
        hiter⟩

end LFunctions
end Boundary
