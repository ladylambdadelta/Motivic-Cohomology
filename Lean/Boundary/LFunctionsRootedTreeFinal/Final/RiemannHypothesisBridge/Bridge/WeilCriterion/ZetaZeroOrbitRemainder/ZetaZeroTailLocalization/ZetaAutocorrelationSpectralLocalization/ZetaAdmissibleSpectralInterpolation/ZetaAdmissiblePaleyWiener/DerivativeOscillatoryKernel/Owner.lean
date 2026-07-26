import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.VerticalIBPIdentity.Owner

/-!
# Paley-Wiener derivative oscillatory kernels

This file owns the derivative-source oscillatory kernels and their zero-order
compact-support Fourier bounds.
-/

open scoped Real
open MeasureTheory

namespace Boundary
namespace LFunctions

open ZetaAdmissibleFunction

/-- The complex zero norm is bounded by any positive real constant. -/
theorem complex_norm_zero_le_of_pos (C : ℝ) (hCpos : 0 < C) :
    ‖(0 : ℂ)‖ ≤ C :=
  Eq.subst
    (motive := fun v : ℝ => v ≤ C)
    (norm_zero : ‖(0 : ℂ)‖ = (0 : ℝ)).symm
    (le_of_lt hCpos)

/-- The derivative-source oscillatory kernel used in the post-IBP Fourier integral. -/
noncomputable def zetaPaleyWienerDerivativeOscillatoryKernel
    (f : ZetaAdmissibleFunction) (x y t : ℝ) : ℂ :=
  zetaPaleyWienerVerticalLineIBPDerivative f x t *
    zetaPaleyWienerVerticalOscillation y t

/-- The named derivative-source oscillatory kernel integrates to the post-IBP integral. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_integral_eq
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    (∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t) =
      zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  rfl

/-- The named derivative-source oscillatory kernel is integrable. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_integrable
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    Integrable
      (fun t : ℝ => zetaPaleyWienerDerivativeOscillatoryKernel f x y t) := by
  exact zetaPaleyWienerVerticalLineIBPDerivative_integrable f x y

/-- The derivative-source oscillatory kernel is zero away from the original source support. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_eq_zero_of_not_mem_source
    (f : ZetaAdmissibleFunction) (x y t : ℝ)
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerDerivativeOscillatoryKernel f x y t = 0 := by
  have hderiv :
      zetaPaleyWienerVerticalLineIBPDerivative f x t = 0 :=
    zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_not_mem_source
      f x t ht
  unfold zetaPaleyWienerDerivativeOscillatoryKernel
  exact Eq.trans
    (congrArg
      (fun v : ℂ => v * zetaPaleyWienerVerticalOscillation y t)
      hderiv)
    (zero_mul (zetaPaleyWienerVerticalOscillation y t))

/-- A pointwise derivative-source bound on the source support dominates the oscillatory
kernel by the source-support indicator. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_norm_le_supportIndicatorBound
    (f : ZetaAdmissibleFunction) (x y B : ℝ)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ B) :
    ∀ t : ℝ,
      ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
        zetaPaleyWienerSupportIndicatorBound f B t := by
  intro t
  by_cases ht : t ∈ tsupport f.toZetaTestFunction
  · have hkernel_le :
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ := by
      unfold zetaPaleyWienerDerivativeOscillatoryKernel
      exact norm_mul_zetaPaleyWienerVerticalOscillation_le
        (zetaPaleyWienerVerticalLineIBPDerivative f x t) y t
    have hsource_bound :
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ B :=
      hbound t ht
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = B := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_mem ht (fun _ : ℝ => B)
    exact Eq.subst
      (motive := fun v : ℝ =>
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤ v)
      hindicator.symm
      (le_trans hkernel_le hsource_bound)
  · have hkernel_zero :
        zetaPaleyWienerDerivativeOscillatoryKernel f x y t = 0 :=
      zetaPaleyWienerDerivativeOscillatoryKernel_eq_zero_of_not_mem_source
        f x y t ht
    have hnorm_zero :
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ = 0 :=
      (congrArg (fun v : ℂ => ‖v‖) hkernel_zero).trans norm_zero
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = 0 := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_not_mem ht (fun _ : ℝ => B)
    exact Eq.subst
      (motive := fun v : ℝ =>
        v ≤ zetaPaleyWienerSupportIndicatorBound f B t)
      hnorm_zero.symm
      (Eq.subst
        (motive := fun v : ℝ => 0 ≤ v)
        hindicator.symm
        le_rfl)

/-- Integrating a derivative-source support-indicator majorant bounds the norm of the
post-IBP oscillatory integral. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_norm_integral_le_supportIndicatorIntegral
    (f : ZetaAdmissibleFunction) (x y B : ℝ)
    (hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t) :
    ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
      ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t := by
  have hnorm :
      ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
        ∫ t : ℝ, ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ :=
    complex_norm_integral_le_integral_norm_of_integrable
      (fun t : ℝ => zetaPaleyWienerDerivativeOscillatoryKernel f x y t)
      (zetaPaleyWienerDerivativeOscillatoryKernel_integrable f x y)
  have hmajorant :
      (∫ t : ℝ, ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖) ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    real_integral_mono_of_integrable_pointwise_le
      (fun t : ℝ => ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖)
      (zetaPaleyWienerSupportIndicatorBound f B)
      (zetaPaleyWienerDerivativeOscillatoryKernel_integrable f x y).norm
      (zetaPaleyWienerSupportIndicatorBound_integrable f B)
      hindicator
  exact le_trans hnorm hmajorant

/-- A uniform pointwise derivative-source bound gives a compact-support integral bound for
the derivative-source oscillatory integral. -/
theorem zetaPaleyWienerDerivativeOscillatoryKernel_integral_norm_le_intervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y B : ℝ) (hB_nonneg : 0 ≤ B)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ B) :
    ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerDerivativeOscillatoryKernel_norm_le_supportIndicatorBound
      f x y B hbound
  have hintegral :
      ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerDerivativeOscillatoryKernel_norm_integral_le_supportIndicatorIntegral
      f x y B hindicator
  have hlength :
      (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerSupportIndicatorIntegral_le_intervalLength_mul_bound
      f I B hB_nonneg
  exact le_trans hintegral hlength

/-- The displayed post-IBP derivative integral is bounded by the compact support length
times any uniform pointwise derivative-source bound. -/
theorem zetaPaleyWienerVerticalLineIBPDerivativeIntegral_norm_le_intervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y B : ℝ) (hB_nonneg : 0 ≤ B)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ B) :
    ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y‖ ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hkernel :
      ‖∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t‖ ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerDerivativeOscillatoryKernel_integral_norm_le_intervalLength_mul_bound
      f I x y B hB_nonneg hbound
  exact Eq.subst
    (motive := fun v : ℂ => ‖v‖ ≤ B * zetaPaleyWienerSupportIntervalLength I)
    (zetaPaleyWienerDerivativeOscillatoryKernel_integral_eq f x y)
    hkernel

/-- The oscillatory kernel attached to an arbitrary iterated horizontal-twist derivative. -/
noncomputable def zetaPaleyWienerIteratedDerivativeOscillatoryKernel
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y t : ℝ) : ℂ :=
  zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t *
    zetaPaleyWienerVerticalOscillation y t

/-- The oscillatory integral attached to an arbitrary iterated horizontal-twist derivative. -/
noncomputable def zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y : ℝ) : ℂ :=
  ∫ t : ℝ, zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t

/-- The first iterated-derivative oscillatory kernel is the named post-IBP derivative
oscillatory kernel. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_one
    (f : ZetaAdmissibleFunction) (x y t : ℝ) :
    zetaPaleyWienerIteratedDerivativeOscillatoryKernel f 1 x y t =
      zetaPaleyWienerDerivativeOscillatoryKernel f x y t := by
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
  unfold zetaPaleyWienerDerivativeOscillatoryKernel
  exact congrArg
    (fun v : ℂ => v * zetaPaleyWienerVerticalOscillation y t)
    (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)

/-- The first iterated-derivative oscillatory integral is the post-IBP derivative integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_one
    (f : ZetaAdmissibleFunction) (x y : ℝ) :
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f 1 x y =
      zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  have hkernel :
      (∫ t : ℝ, zetaPaleyWienerIteratedDerivativeOscillatoryKernel f 1 x y t) =
        ∫ t : ℝ, zetaPaleyWienerDerivativeOscillatoryKernel f x y t :=
    complex_integral_congr_of_pointwise_eq
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f 1 x y t)
      (fun t : ℝ => zetaPaleyWienerDerivativeOscillatoryKernel f x y t)
      (zetaPaleyWienerIteratedDerivativeOscillatoryKernel_one f x y)
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
  exact hkernel.trans (zetaPaleyWienerDerivativeOscillatoryKernel_integral_eq f x y)

/-- The arbitrary iterated-derivative oscillatory kernel is zero away from the original
source support. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_eq_zero_of_not_mem_source
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y t : ℝ)
    (ht : t ∉ tsupport f.toZetaTestFunction) :
    zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t = 0 := by
  have hderiv :
      zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t = 0 :=
    zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_not_mem_source
      f n x t ht
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
  exact Eq.trans
    (congrArg
      (fun v : ℂ => v * zetaPaleyWienerVerticalOscillation y t)
      hderiv)
    (zero_mul (zetaPaleyWienerVerticalOscillation y t))

/-- A pointwise bound for the `n`th derivative source dominates the corresponding
oscillatory kernel by the source-support indicator. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_norm_le_supportIndicatorBound
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y B : ℝ)
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t‖ ≤ B) :
    ∀ t : ℝ,
      ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤
        zetaPaleyWienerSupportIndicatorBound f B t := by
  intro t
  by_cases ht : t ∈ tsupport f.toZetaTestFunction
  · have hkernel_le :
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤
          ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t‖ := by
      unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
      exact norm_mul_zetaPaleyWienerVerticalOscillation_le
        (zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) y t
    have hsource_bound :
        ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t‖ ≤ B :=
      hbound t ht
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = B := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_mem ht (fun _ : ℝ => B)
    exact Eq.subst
      (motive := fun v : ℝ =>
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤ v)
      hindicator.symm
      (le_trans hkernel_le hsource_bound)
  · have hkernel_zero :
        zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t = 0 :=
      zetaPaleyWienerIteratedDerivativeOscillatoryKernel_eq_zero_of_not_mem_source
        f n x y t ht
    have hnorm_zero :
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ = 0 :=
      (congrArg (fun v : ℂ => ‖v‖) hkernel_zero).trans norm_zero
    have hindicator :
        zetaPaleyWienerSupportIndicatorBound f B t = 0 := by
      unfold zetaPaleyWienerSupportIndicatorBound
      exact Set.indicator_of_not_mem ht (fun _ : ℝ => B)
    exact Eq.subst
      (motive := fun v : ℝ =>
        v ≤ zetaPaleyWienerSupportIndicatorBound f B t)
      hnorm_zero.symm
      (Eq.subst
        (motive := fun v : ℝ => 0 ≤ v)
        hindicator.symm
        le_rfl)

/-- The arbitrary iterated horizontal-twist derivative source is continuous. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_continuous
    (f : ZetaAdmissibleFunction) (n : ℕ) (x : ℝ) :
    Continuous
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) := by
  have hjet_plane :
      Continuous
        (fun p : ℝ × ℝ =>
          zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2) :=
    zetaPaleyWienerHorizontalTwistVerticalJet_continuous f n
  have hline :
      Continuous (fun t : ℝ => (x, t)) :=
    continuous_const.prod_mk continuous_id
  have hjet_line :
      Continuous
        (fun t : ℝ => zetaPaleyWienerHorizontalTwistVerticalJet f n x t) :=
    hjet_plane.comp hline
  have hfun :
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) =
        fun t : ℝ => zetaPaleyWienerHorizontalTwistVerticalJet f n x t :=
    funext
      (fun t : ℝ =>
        zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet f n x t)
  exact Eq.subst
    (motive := fun g : ℝ → ℂ => Continuous g)
    hfun.symm
    hjet_line

/-- The arbitrary iterated horizontal-twist derivative source has compact support. -/
theorem zetaPaleyWienerHorizontalTwistIteratedDerivative_hasCompactSupport
    (f : ZetaAdmissibleFunction) (n : ℕ) (x : ℝ) :
    HasCompactSupport
      (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) := by
  induction n with
  | zero =>
      have hfun :
          (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t) =
            fun t : ℝ => zetaPaleyWienerHorizontalTwist f x t :=
        funext (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative_zero f x t)
      exact Eq.subst
        (motive := fun g : ℝ → ℂ => HasCompactSupport g)
        hfun.symm
        (zetaPaleyWienerHorizontalTwist_hasCompactSupport f x)
  | succ n ih =>
      have hderiv :
          HasCompactSupport
            (deriv
              (fun t : ℝ =>
                zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t)) :=
        ih.deriv
      have hfun :
          (fun t : ℝ =>
            zetaPaleyWienerHorizontalTwistIteratedDerivative f (Nat.succ n) x t) =
            deriv
              (fun t : ℝ =>
                zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) :=
        funext (fun t : ℝ =>
          zetaPaleyWienerHorizontalTwistIteratedDerivative_succ f n x t)
      exact Eq.subst
        (motive := fun g : ℝ → ℂ => HasCompactSupport g)
        hfun.symm
        hderiv

/-- The arbitrary iterated-derivative oscillatory kernel is continuous. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_continuous
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y : ℝ) :
    Continuous
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t) := by
  have hderiv :
      Continuous
        (fun t : ℝ => zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t) :=
    zetaPaleyWienerHorizontalTwistIteratedDerivative_continuous f n x
  have hosc :
      Continuous (fun t : ℝ => zetaPaleyWienerVerticalOscillation y t) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal)
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
  exact hderiv.mul hosc

/-- The arbitrary iterated-derivative oscillatory kernel has compact support. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryKernel_hasCompactSupport
    (f : ZetaAdmissibleFunction) (n : ℕ) (x y : ℝ) :
    HasCompactSupport
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t) := by
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryKernel
  exact (zetaPaleyWienerHorizontalTwistIteratedDerivative_hasCompactSupport
    f n x).mul_right

/-- A uniform pointwise bound for the `n`th derivative source gives a compact-support
integral bound for the corresponding oscillatory integral. -/
theorem zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_norm_le_intervalLength_mul_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (n : ℕ) (x y B : ℝ) (hB_nonneg : 0 ≤ B)
    (hintegrable :
      Integrable
        (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t))
    (hbound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f n x t‖ ≤ B) :
    ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f n x y‖ ≤
      B * zetaPaleyWienerSupportIntervalLength I := by
  have hindicator :
      ∀ t : ℝ,
        ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤
          zetaPaleyWienerSupportIndicatorBound f B t :=
    zetaPaleyWienerIteratedDerivativeOscillatoryKernel_norm_le_supportIndicatorBound
      f n x y B hbound
  have hnorm :
      ‖∫ t : ℝ, zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ ≤
        ∫ t : ℝ, ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖ :=
    complex_norm_integral_le_integral_norm_of_integrable
      (fun t : ℝ => zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t)
      hintegrable
  have hmajorant :
      (∫ t : ℝ, ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖) ≤
        ∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t :=
    real_integral_mono_of_integrable_pointwise_le
      (fun t : ℝ => ‖zetaPaleyWienerIteratedDerivativeOscillatoryKernel f n x y t‖)
      (zetaPaleyWienerSupportIndicatorBound f B)
      hintegrable.norm
      (zetaPaleyWienerSupportIndicatorBound_integrable f B)
      hindicator
  have hlength :
      (∫ t : ℝ, zetaPaleyWienerSupportIndicatorBound f B t) ≤
        B * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerSupportIndicatorIntegral_le_intervalLength_mul_bound
      f I B hB_nonneg
  unfold zetaPaleyWienerIteratedDerivativeOscillatoryIntegral
  exact le_trans hnorm (le_trans hmajorant hlength)

/-- Uniform compact-strip seminorm control for the zero-th horizontal-twist derivative. -/
theorem exists_zetaPaleyWienerHorizontalTwistIteratedDerivative_zero_uniformSeminorm
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t‖ ≤ C := by
  let C : ℝ :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b 0
  have hCpos : 0 < C :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_pos f I a b 0
  exact
    ⟨C, hCpos,
      fun x hxLeft hxRight t =>
        match zetaPaleyWienerSupportInterval_inside_or_outside I t with
        | Or.inl hinside =>
            let hjet :
                ‖zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t‖ ≤ C :=
              zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_bound
                f I a b 0 (x, t) ⟨⟨hxLeft, hxRight⟩, hinside⟩
            Eq.subst
              (motive := fun v : ℂ => ‖v‖ ≤ C)
              (zetaPaleyWienerHorizontalTwistIteratedDerivative_zero_eq_verticalJet_zero
                f x t).symm
              hjet
        | Or.inr houtside =>
            match houtside with
            | Or.inl hbelow =>
                let hzero :
                    zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t = 0 :=
                  zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_off_supportInterval
                    f I 0 x t hbelow
                Eq.subst
                  (motive := fun v : ℂ => ‖v‖ ≤ C)
                  hzero.symm
                  (complex_norm_zero_le_of_pos C hCpos)
            | Or.inr habove =>
                let hzero :
                    zetaPaleyWienerHorizontalTwistIteratedDerivative f 0 x t = 0 :=
                  zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
                    f I 0 x t habove
                Eq.subst
                  (motive := fun v : ℂ => ‖v‖ ≤ C)
                  hzero.symm
                  (complex_norm_zero_le_of_pos C hCpos)⟩

/-- Uniform seminorm control for the iterated horizontal-twist derivative family on compact
real-part strips and the fixed compact support interval. -/
theorem exists_zetaPaleyWienerHorizontalTwistIteratedDerivative_uniformSeminorm
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f N x t‖ ≤ C := by
  let C : ℝ :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b N
  have hCpos : 0 < C :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_pos f I a b N
  exact
    ⟨C, hCpos,
      fun x hxLeft hxRight t =>
        match zetaPaleyWienerSupportInterval_inside_or_outside I t with
        | Or.inl hinside =>
            let hjet :
                ‖zetaPaleyWienerHorizontalTwistVerticalJet f N x t‖ ≤ C :=
              zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_bound
                f I a b N (x, t) ⟨⟨hxLeft, hxRight⟩, hinside⟩
            Eq.subst
              (motive := fun v : ℂ => ‖v‖ ≤ C)
              (zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet
                f N x t).symm
              hjet
        | Or.inr houtside =>
            match houtside with
            | Or.inl hbelow =>
                let hzero :
                    zetaPaleyWienerHorizontalTwistIteratedDerivative f N x t = 0 :=
                  zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_off_supportInterval
                    f I N x t hbelow
                Eq.subst
                  (motive := fun v : ℂ => ‖v‖ ≤ C)
                  hzero.symm
                  (complex_norm_zero_le_of_pos C hCpos)
            | Or.inr habove =>
                let hzero :
                    zetaPaleyWienerHorizontalTwistIteratedDerivative f N x t = 0 :=
                  zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
                    f I N x t habove
                Eq.subst
                  (motive := fun v : ℂ => ‖v‖ ≤ C)
                  hzero.symm
                  (complex_norm_zero_le_of_pos C hCpos)⟩

/-- Uniform seminorm control for the first horizontal-twist derivative family on compact real-part strips. -/
theorem exists_zetaPaleyWienerHorizontalTwistDerivative_uniformSeminorm
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C := by
  let C : ℝ :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b 1
  have hCpos : 0 < C :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_pos f I a b 1
  exact
    ⟨C, hCpos,
      fun x hxLeft hxRight t =>
        match zetaPaleyWienerSupportInterval_inside_or_outside I t with
        | Or.inl hinside =>
            let hjet :
                ‖zetaPaleyWienerHorizontalTwistVerticalJet f 1 x t‖ ≤ C :=
              zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_bound
                f I a b 1 (x, t) ⟨⟨hxLeft, hxRight⟩, hinside⟩
            let hiterated :
                ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t‖ ≤ C :=
              Eq.subst
                (motive := fun v : ℂ => ‖v‖ ≤ C)
                (zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_verticalJet
                  f 1 x t).symm
                hjet
            Eq.subst
              (motive := fun v : ℂ => ‖v‖ ≤ C)
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
                    ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t‖ ≤ C :=
                  Eq.subst
                    (motive := fun v : ℂ => ‖v‖ ≤ C)
                    hzero.symm
                    (complex_norm_zero_le_of_pos C hCpos)
                Eq.subst
                  (motive := fun v : ℂ => ‖v‖ ≤ C)
                  (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)
                  hiterated
            | Or.inr habove =>
                let hzero :
                    zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t = 0 :=
                  zetaPaleyWienerHorizontalTwistIteratedDerivative_eq_zero_of_supportInterval_lt
                    f I 1 x t habove
                let hiterated :
                    ‖zetaPaleyWienerHorizontalTwistIteratedDerivative f 1 x t‖ ≤ C :=
                  Eq.subst
                    (motive := fun v : ℂ => ‖v‖ ≤ C)
                    hzero.symm
                    (complex_norm_zero_le_of_pos C hCpos)
                Eq.subst
                  (motive := fun v : ℂ => ‖v‖ ≤ C)
                  (zetaPaleyWienerHorizontalTwistIteratedDerivative_one f x t)
                  hiterated⟩

/-- Raw compact-support bound for the post-IBP derivative Fourier integral. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_le_rawBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hbound :
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤
        C * zetaPaleyWienerSupportIntervalLength I := by
  intro x y hx_left hx_right
  have hsource_bound :
      ∀ t : ℝ,
        t ∈ tsupport f.toZetaTestFunction →
        ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C := by
    intro t _ht
    exact hbound x hx_left hx_right t
  exact zetaPaleyWienerVerticalLineIBPDerivativeIntegral_norm_le_intervalLength_mul_bound
    f I x y C hC_nonneg hsource_bound

/-- Bumped compact-support bound for the post-IBP derivative Fourier integral. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_le_bumpedBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b C : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hbound :
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤
        C * zetaPaleyWienerSupportIntervalLength I + 1 := by
  intro x y hx_left hx_right
  have hraw :
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖ ≤
        C * zetaPaleyWienerSupportIntervalLength I :=
    zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_le_rawBound
      f I a b C hC_nonneg hbound x y hx_left hx_right
  have hle :
      C * zetaPaleyWienerSupportIntervalLength I ≤
        C * zetaPaleyWienerSupportIntervalLength I + 1 :=
    le_add_of_nonneg_right zero_le_one
  exact le_trans hraw hle

/-- Zero-order Fourier bound for the compactly supported horizontal-twist derivative
family. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrder_uniformBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖ ≤ C := by
  let C0 : ℝ :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope f I a b 1
  have hC0pos : 0 < C0 :=
    zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_pos f I a b 1
  let hC0bound :
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          ‖zetaPaleyWienerVerticalLineIBPDerivative f x t‖ ≤ C0 :=
    fun x hxLeft hxRight t =>
      match zetaPaleyWienerSupportInterval_inside_or_outside I t with
      | Or.inl hinside =>
          let hjet :
              ‖zetaPaleyWienerHorizontalTwistVerticalJet f 1 x t‖ ≤ C0 :=
            zetaPaleyWienerHorizontalTwistVerticalJetRectangleEnvelope_bound
              f I a b 1 (x, t) ⟨⟨hxLeft, hxRight⟩, hinside⟩
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
  exact
    ⟨C, hCpos,
      fun x y hxLeft hxRight =>
        zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_le_bumpedBound
          f I a b C0 hC0_nonneg hC0bound x y hxLeft hxRight⟩

end LFunctions
end Boundary
