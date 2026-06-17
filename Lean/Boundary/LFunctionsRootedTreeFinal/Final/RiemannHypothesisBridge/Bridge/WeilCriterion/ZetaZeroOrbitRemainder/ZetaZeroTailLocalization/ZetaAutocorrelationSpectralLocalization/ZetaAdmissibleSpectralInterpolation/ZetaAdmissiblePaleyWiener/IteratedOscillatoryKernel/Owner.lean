import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.LowFrequencyDecay.Owner

/-!
# Paley-Wiener iterated oscillatory kernels

This file owns the arbitrary iterated-derivative oscillatory kernels, repeated
vertical integration by parts, and the resulting vertical-strip rapid decay
wrappers. It is copy-first extracted from the current Paley-Wiener owner file
and is not imported by that parent yet, so declaration names intentionally match
the existing owner surface.
-/

open scoped Real
open MeasureTheory

namespace Boundary
namespace LFunctions

/-- The arbitrary iterated-derivative oscillatory kernel is integrable. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y : ℝ) :
    Integrable
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t) := by
  exact (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_continuous
    f n x y).integrable_of_hasCompactSupport
      (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_hasCompactSupport f n x y)

/-- Zero-order compact-support bound for arbitrary iterated horizontal-twist derivative
oscillatory integrals. -/
/-- Helper for uniform bound: extract witness and basic inequalities. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrder_uniformBound_witness
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤ C := by
  match exists_zetaPaleyWienerHorizontalTwistIteratedDerivative_uniformSeminorm
      f I a b start with
  | ⟨C0, hC0pos, hC0bound⟩ =>
      let C : ℝ := C0 * zetaPaleyWienerSupportIntervalLength I + 1
      have hC0_nonneg : 0 ≤ C0 :=
        le_of_lt hC0pos
      have hraw_nonneg :
          0 ≤ C0 * zetaPaleyWienerSupportIntervalLength I :=
        mul_nonneg hC0_nonneg (zetaPaleyWienerSupportIntervalLength_nonnegative I)
      have hCpos : 0 < C :=
        lt_of_le_of_lt hraw_nonneg
          (lt_add_of_pos_right
            (C0 * zetaPaleyWienerSupportIntervalLength I)
            zero_lt_one)
      exact ⟨C, hCpos, fun x y hx_left hx_right =>
        let hsource_bound : ∀ t : ℝ,
            t ∈ tsupport f.toZetaTestFunction →
            ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t‖ ≤ C0 :=
          fun t _ht => hC0bound x hx_left hx_right t
        let hraw :
            ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤
              C0 * zetaPaleyWienerSupportIntervalLength I :=
          zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_intervalLength_mul_bound
            f I start x y C0 hC0_nonneg
            (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_integrable f start x y)
            hsource_bound
        let hle :
            C0 * zetaPaleyWienerSupportIntervalLength I ≤
              C0 * zetaPaleyWienerSupportIntervalLength I + 1 :=
          le_add_of_nonneg_right zero_le_one
        le_trans hraw hle⟩

theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrder_uniformBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤ C :=
  zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrder_uniformBound_witness
    f I a b start

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
  match zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_zeroOrder_uniformBound
      f I a b start with
  | ⟨C, hCpos, hCbound⟩ =>
      let hweight_eq : (y : ℝ) → C * (1 + ‖y‖) ^ (-(0 : ℤ)) = C :=
        fun y => Eq.trans
          (congrArg (fun v : ℝ => C * v) (zetaPaleyWiener_zeroDecayWeight y))
          (mul_one C)
      exact ⟨C, hCpos, fun x y hx_left hx_right _hy =>
        Eq.subst
          (motive := fun v : ℝ =>
            ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖ ≤ v)
          (hweight_eq y).symm
          (hCbound x y hx_left hx_right)⟩

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
    Function.ext hfun_eq
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
  exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_contDiff
    f start x).differentiable le_top t

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
    _ = 0 := sub_zero 0

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
    Function.ext fun t =>
      calc H t * (A * V t)
        = (H t * A) * V t := by
          exact (mul_assoc (H t) A (V t)).symm
        _ = (A * H t) * V t := by
          exact congrArg (fun v : ℂ => v * V t) (mul_comm (H t) A)
        _ = A * (H t * V t) := by
          exact mul_assoc A (H t) (V t)
  have hintegral :
      (∫ t : ℝ, H t * (A * V t)) =
        A * ∫ t : ℝ, H t * V t := by
    exact Eq.trans
      (congrArg
        (fun q : ℝ → ℂ => ∫ t : ℝ, q t)
        hright_integrand)
      (integral_const_mul A (fun t : ℝ => H t * V t))
  have hdefs : zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y =
      ∫ t : ℝ, zetaPaleyWienerHorizontalTwistIteratedDerivative f start x t *
        zetaPaleyWienerVerticalOscillation y t := by
    rfl
  exact hdefs ▸ hintegral.symm

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

/-- One high-frequency integration-by-parts step for arbitrary iterated derivative
oscillatory integrals, stated as a recurrence from the next derivative source. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_successor_from_next_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (start N : ℕ)
    (hnext :
      ∃ C : ℝ,
        0 < C ∧
        ∀ x y : ℝ,
          a ≤ x →
          x ≤ b →
          1 ≤ ‖y‖ →
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
            ≤ C * (1 + ‖y‖) ^ (-(N : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f start x y‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  match hnext with
  | ⟨C, hCpos, hCbound⟩ =>
      exact ⟨C * 2, mul_pos hCpos zero_lt_two,
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_successor_bound
          f I a b start N C hCpos hCbound⟩

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
  induction N generalizing start with
  | zero =>
      exact zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_zeroOrder_decay
        f I a b start
  | succ N ih =>
      have hnext :
          ∃ C : ℝ,
            0 < C ∧
            ∀ x y : ℝ,
              a ≤ x →
              x ≤ b →
              1 ≤ ‖y‖ →
              ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f (start + 1) x y‖
                ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) :=
        ih (start + 1)
      exact
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_successor_from_next_decay
          f I a b start N hnext

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
  match zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequency_decay
      f I a b 1 (Nat.succ N) with
  | ⟨C, hCpos, hCbound⟩ =>
      exact ⟨C, hCpos, fun x y hx_left hx_right hy =>
        let hiter :
            ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f 1 x y‖
              ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
          hCbound x y hx_left hx_right hy
        Eq.subst
          (motive := fun v : ℂ =>
            ‖v‖ ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
          (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_one f x y)
          hiter⟩

/-- Low- and high-frequency positive-order estimates combine into the global estimate. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_from_low_high
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ)
    (hlow :
      ∃ C : ℝ,
        0 < C ∧
        ∀ x y : ℝ,
          a ≤ x →
          x ≤ b →
          ‖y‖ ≤ 1 →
          ‖∫ t : ℝ,
            zetaPaleyWienerVerticalLineIBPDerivative f x t *
              zetaPaleyWienerVerticalOscillation y t‖
            ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
    (hhigh :
      ∃ C : ℝ,
        0 < C ∧
        ∀ x y : ℝ,
          a ≤ x →
          x ≤ b →
          1 ≤ ‖y‖ →
          ‖∫ t : ℝ,
            zetaPaleyWienerVerticalLineIBPDerivative f x t *
              zetaPaleyWienerVerticalOscillation y t‖
            ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  match hlow, hhigh with
  | ⟨Clow, hClow_pos, hClow⟩, ⟨Chigh, hChigh_pos, hChigh⟩ =>
      exact ⟨max Clow Chigh, lt_of_lt_of_le hClow_pos (le_max_left Clow Chigh),
        fun x y hx_left hx_right => by
          have hweight :
              0 ≤ (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
            zetaPaleyWiener_realVerticalDecayWeight_nonnegative y (Nat.succ N)
          by_cases hlow_region : ‖y‖ ≤ 1
          · have hbound :
                ‖∫ t : ℝ,
                  zetaPaleyWienerVerticalLineIBPDerivative f x t *
                    zetaPaleyWienerVerticalOscillation y t‖
                  ≤ Clow * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
              hClow x y hx_left hx_right hlow_region
            have hconstant :
                Clow * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) ≤
                  max Clow Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
              mul_le_mul_of_nonneg_right (le_max_left Clow Chigh) hweight
            exact hbound.trans hconstant
          · have hhigh_region : 1 ≤ ‖y‖ :=
              le_of_lt (lt_of_not_ge hlow_region)
            have hbound :
                ‖∫ t : ℝ,
                  zetaPaleyWienerVerticalLineIBPDerivative f x t *
                    zetaPaleyWienerVerticalOscillation y t‖
                  ≤ Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
              hChigh x y hx_left hx_right hhigh_region
            have hconstant :
                Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) ≤
                  max Clow Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
              mul_le_mul_of_nonneg_right (le_max_right Clow Chigh) hweight
            exact hbound.trans hconstant⟩

/-- Positive-order Fourier decay for the compactly supported horizontal-twist derivative
family is the repeated-integration-by-parts estimate. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_uniformDecay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) := by
  exact zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_from_low_high
    f I a b N
    (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_lowFrequency
      f I a b N)
    (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_highFrequency
      f I a b N)

/-- Fourier decay for the compactly supported horizontal-twist derivative family, with
constants uniform over the real-part strip. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformDecay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) := by
  cases N with
  | zero =>
      exact zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformDecay
        f I a b
  | succ N =>
      exact zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_uniformDecay
        f I a b N

/-- Uniform compact-strip decay for the derivative integral produced by vertical-line
integration by parts, expressed directly in the real line coordinates `(x,y)`. -/
theorem zetaPaleyWienerVerticalLineIBPDerivativeIntegral_compactStrip_uniformDecay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y‖
          ≤ C * (1 + ‖y‖) ^ (-(N : ℤ)) := by
  match zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformDecay
      f I a b N with
  | ⟨C, hCpos, hCbound⟩ =>
      exact ⟨C, hCpos, fun x y hx_left hx_right =>
        hCbound x y hx_left hx_right⟩

/-- Uniform compact-strip control of the derivative integral produced by one vertical-line
integration-by-parts step.

The derivative source depends on `x = re z`, but `x` ranges over the compact interval
`[a,b]`, so the resulting derivative-integral constants can be made uniform across the
whole strip. -/
theorem zetaPaleyWienerVerticalLineIBPDerivativeIntegral_supportInterval_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖
          ≤ C * zetaPaleyWienerVerticalWeight z N := by
  match zetaPaleyWienerVerticalLineIBPDerivativeIntegral_compactStrip_uniformDecay
      f I a b N with
  | ⟨C, hCpos, hCbound⟩ =>
      exact ⟨C, hCpos, fun z hz =>
        hCbound z.re z.im hz.1 hz.2⟩

/-- High-frequency Paley-Wiener control from vertical-line integration by parts on a compact
real-part strip.

The honest strip argument does not produce one derivative probe independent of `z`.  On the
vertical line `re z = x`, integration by parts differentiates the compactly supported source
after multiplying by the horizontal factor `Real.exp (x * t)`, and the constants are then made
uniform for `x ∈ [a,b]`.  This theorem owns that compact-strip vertical-line transport. -/
theorem zetaLaplaceTransform_supportInterval_successor_highFrequency_decay_from_verticalLineIBP
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        1 ≤ ‖z.im‖ →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  match zetaPaleyWienerVerticalLineIBPDerivativeIntegral_supportInterval_decay
      f I a b N with
  | ⟨C, hC_pos, hC⟩ =>
      exact ⟨C * 2, mul_pos hC_pos zero_lt_two, fun z hzstrip hzhigh =>
        let hparts :
            ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
              ‖(z.im : ℂ)⁻¹‖ *
                ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ :=
          zetaLaplaceTransform_supportInterval_verticalLineIBP_normComparison
            f I a b z hzstrip hzhigh
        let hderivativeBound :
            ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖
              ≤ C * zetaPaleyWienerVerticalWeight z N :=
          hC z hzstrip
        let hinv_nonneg : 0 ≤ ‖(z.im : ℂ)⁻¹‖ :=
          norm_nonneg ((z.im : ℂ)⁻¹)
        let hboundWithInv :
            ‖(z.im : ℂ)⁻¹‖ *
                ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖
              ≤ ‖(z.im : ℂ)⁻¹‖ *
                (C * zetaPaleyWienerVerticalWeight z N) :=
          mul_le_mul_of_nonneg_left hderivativeBound hinv_nonneg
        let hC_nonneg : 0 ≤ C :=
          le_of_lt hC_pos
        let hweight :
            ‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N ≤
              2 * zetaPaleyWienerVerticalWeight z (N + 1) :=
          zetaPaleyWiener_inverseIm_mul_weight_le_successor_highFrequency z N hzhigh
        let hrearrange :
            ‖(z.im : ℂ)⁻¹‖ * (C * zetaPaleyWienerVerticalWeight z N) =
              C * (‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N) := by
          calc
            ‖(z.im : ℂ)⁻¹‖ * (C * zetaPaleyWienerVerticalWeight z N) =
                (‖(z.im : ℂ)⁻¹‖ * C) * zetaPaleyWienerVerticalWeight z N := by
              exact (mul_assoc ‖(z.im : ℂ)⁻¹‖ C
                (zetaPaleyWienerVerticalWeight z N)).symm
            _ = (C * ‖(z.im : ℂ)⁻¹‖) * zetaPaleyWienerVerticalWeight z N := by
              exact congrArg (fun y : ℝ => y * zetaPaleyWienerVerticalWeight z N)
                (mul_comm ‖(z.im : ℂ)⁻¹‖ C)
            _ = C * (‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N) := by
              exact mul_assoc C ‖(z.im : ℂ)⁻¹‖
                (zetaPaleyWienerVerticalWeight z N)
        let hrenorm :
            C * (‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N) ≤
              C * (2 * zetaPaleyWienerVerticalWeight z (N + 1)) :=
          mul_le_mul_of_nonneg_left hweight hC_nonneg
        let htarget :
            C * (2 * zetaPaleyWienerVerticalWeight z (N + 1)) =
              (C * 2) * zetaPaleyWienerVerticalWeight z (N + 1) := by
          exact (mul_assoc C 2 (zetaPaleyWienerVerticalWeight z (N + 1))).symm
        hparts.trans (hboundWithInv.trans (Eq.subst
          (motive := fun y : ℝ => y ≤ (C * 2) * zetaPaleyWienerVerticalWeight z (N + 1))
          hrearrange.symm
          (hrenorm.trans_eq htarget)))⟩

/-- Low-frequency successor transport: on `|im z| ≤ 1`, the current decay estimate can be
renormalized into the successor estimate by enlarging the constant. -/
theorem zetaLaplaceTransform_supportInterval_successor_lowFrequency_decay_from_current
    (f : ZetaAdmissibleFunction)
    (a b : ℝ) (N : ℕ)
    (hcurrent :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z N) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖z.im‖ ≤ 1 →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  match hcurrent with
  | ⟨C, hC_pos, hC⟩ =>
      exact ⟨C * 2, mul_pos hC_pos zero_lt_two, fun z hzstrip hzlow =>
        let hbound :
            ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
              ≤ C * zetaPaleyWienerVerticalWeight z N :=
          hC z hzstrip
        let hweight :
            zetaPaleyWienerVerticalWeight z N ≤
              2 * zetaPaleyWienerVerticalWeight z (N + 1) :=
          zetaPaleyWienerVerticalWeight_le_successor_lowFrequency z N hzlow
        let hC_nonneg : 0 ≤ C :=
          le_of_lt hC_pos
        let hrenorm :
            C * zetaPaleyWienerVerticalWeight z N ≤
              C * (2 * zetaPaleyWienerVerticalWeight z (N + 1)) :=
          mul_le_mul_of_nonneg_left hweight hC_nonneg
        let hreassociate :
            C * (2 * zetaPaleyWienerVerticalWeight z (N + 1)) =
              (C * 2) * zetaPaleyWienerVerticalWeight z (N + 1) := by
          exact (mul_assoc C 2 (zetaPaleyWienerVerticalWeight z (N + 1))).symm
        hbound.trans (hrenorm.trans_eq hreassociate)⟩

/-- The low/high frequency successor estimates combine into the global successor estimate. -/
theorem zetaLaplaceTransform_supportInterval_successor_decay_from_low_high
    (f : ZetaAdmissibleFunction)
    (a b : ℝ) (N : ℕ)
    (hlow :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖z.im‖ ≤ 1 →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z (N + 1))
    (hhigh :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          1 ≤ ‖z.im‖ →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z (N + 1)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  match hlow, hhigh with
  | ⟨Clow, hClow_pos, hClow⟩, ⟨Chigh, hChigh_pos, hChigh⟩ =>
      exact ⟨max Clow Chigh, lt_of_lt_of_le hClow_pos (le_max_left Clow Chigh), fun z hz => by
        let hweight : 0 ≤ zetaPaleyWienerVerticalWeight z (N + 1) :=
          zetaPaleyWienerVerticalWeight_nonnegative z (N + 1)
        by_cases hlow_region : ‖z.im‖ ≤ 1
        · have hbound :
              ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
                ≤ Clow * zetaPaleyWienerVerticalWeight z (N + 1) :=
            hClow z hz hlow_region
          have hconstant :
              Clow * zetaPaleyWienerVerticalWeight z (N + 1) ≤
                max Clow Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
            mul_le_mul_of_nonneg_right (le_max_left Clow Chigh) hweight
          exact hbound.trans hconstant
        · have hhigh_region : 1 ≤ ‖z.im‖ :=
            le_of_lt (lt_of_not_ge hlow_region)
          have hbound :
              ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
                ≤ Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
            hChigh z hz hhigh_region
          have hconstant :
              Chigh * zetaPaleyWienerVerticalWeight z (N + 1) ≤
                max Clow Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right Clow Chigh) hweight
          exact hbound.trans hconstant⟩

/-- One integration-by-parts step for Paley-Wiener control on a fixed compact support
interval.

The step consumes the `N`th vertical decay estimate and produces the successor estimate by
integrating by parts once more; smoothness bounds the next derivative seminorm and compact
support kills the boundary terms. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_successor
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ)
    (hN :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z N) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  have hlow :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖z.im‖ ≤ 1 →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaLaplaceTransform_supportInterval_successor_lowFrequency_decay_from_current
      f a b N hN
  have hhigh :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          1 ≤ ‖z.im‖ →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaLaplaceTransform_supportInterval_successor_highFrequency_decay_from_verticalLineIBP
      f I a b N
  exact zetaLaplaceTransform_supportInterval_successor_decay_from_low_high
    f a b N hlow hhigh

/-- Paley-Wiener decay at a fixed order, uniformly available for every admissible probe.

This is the induction form needed by integration by parts: in the successor step, the
induction hypothesis is applied to the derivative probe, not only to the original probe. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_decay_all
    (N : ℕ) :
    ∀ (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
      (a b : ℝ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          zetaPaleyWienerInVerticalStrip a b z →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * zetaPaleyWienerVerticalWeight z N := by
  induction N with
  | zero =>
      intro f I a b
      exact zetaLaplaceTransform_supportInterval_zeroOrder_decay f I a b
  | succ N ih =>
      intro f I a b
      have hN :
          ∃ C : ℝ,
            0 < C ∧
            ∀ z : ℂ,
              zetaPaleyWienerInVerticalStrip a b z →
              ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
                ≤ C * zetaPaleyWienerVerticalWeight z N :=
        ih f I a b
      exact zetaLaplaceTransform_supportInterval_integrationByParts_successor
        f I a b N hN

/-- The oscillatory integration-by-parts estimate on a fixed support interval.

This is the Fourier-side core of Paley-Wiener: after `N` integrations by parts, the vertical
frequency contributes the factor `(1 + |im z|)^{-N}`.  Smoothness supplies the needed
derivative seminorms and the support-interval vanishing lemmas kill all boundary terms. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_decay
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z N := by
  exact zetaLaplaceTransform_supportInterval_integrationByParts_decay_all
    N f I a b

/-- The Paley-Wiener support-interval estimate assembled from the interval seminorm and the
oscillatory integration-by-parts bound. -/
theorem zetaLaplaceTransform_verticalStripDecayConstant_of_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, zetaLaplaceTransformHasVerticalStripDecayConstant f a b N C := by
  match zetaLaplaceTransform_supportInterval_integrationByParts_decay
      f I a b N with
  | ⟨C, hCpos, hCbound⟩ =>
      exact ⟨C, hCpos, hCbound⟩

/-- The compact-support smooth Paley-Wiener estimate for the Laplace transform from an explicit
support interval, with the decay constant produced as data.

This is the analytic core: use the supplied compact interval, integrate by parts `N` times in the
vertical oscillatory factor, use smoothness to bound the resulting derivative seminorm on the
support, and absorb the bounded horizontal factor uniformly over `a ≤ re z ≤ b`. -/
theorem zetaLaplaceTransform_verticalStripDecayConstant_of_supportInterval_integrationByParts
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, zetaLaplaceTransformHasVerticalStripDecayConstant f a b N C := by
  exact zetaLaplaceTransform_verticalStripDecayConstant_of_supportInterval
    f I a b N

/-- The compact-support smooth Paley-Wiener estimate for the Laplace transform, with the
decay constant produced as data. -/
theorem zetaLaplaceTransform_verticalStripDecayConstant_of_integrationByParts
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, zetaLaplaceTransformHasVerticalStripDecayConstant f a b N C := by
  match exists_zetaPaleyWienerSupportInterval f with
  | ⟨I⟩ =>
      exact zetaLaplaceTransform_verticalStripDecayConstant_of_supportInterval_integrationByParts
        f I a b N

/-- Paley-Wiener rapid vertical-strip decay for the Laplace transform of a compactly
supported smooth admissible source.

This is the exact analytic owner theorem: repeated integration by parts in the
oscillatory factor `exp (I * y * t)` gives arbitrary inverse powers of the
vertical frequency, while compact support makes the horizontal strip factor
uniform on `a ≤ re z ≤ b` and kills all boundary terms. -/
theorem zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  match zetaLaplaceTransform_verticalStripDecayConstant_of_integrationByParts
      f a b N with
  | ⟨C, hC⟩ =>
      exact ⟨C, hC.1, fun z haz hzb =>
        hC.2 z ⟨haz, hzb⟩⟩

/-- Paley-Wiener rapid vertical-strip decay for the completed explicit-formula transform
`Φ_f`, projected as an existence statement for theorem consumers. -/
theorem zetaPhi_verticalStripRapidDecay_of_admissible_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  have hbase :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
    zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
      f a b N
  match hbase with
  | ⟨C, hCpos, hboundBase⟩ =>
      exact ⟨C, hCpos, fun z haz hzb =>
        let hphi :
            zetaCompletedExplicitFormulaPhi f z =
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
          exact congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace f) z
        let hbound :
            ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
              ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
          hboundBase z haz hzb
        Eq.subst
          (motive := fun w : ℂ =>
            ‖w‖ ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)))
          hphi.symm
          hbound⟩

end LFunctions
end Boundary
