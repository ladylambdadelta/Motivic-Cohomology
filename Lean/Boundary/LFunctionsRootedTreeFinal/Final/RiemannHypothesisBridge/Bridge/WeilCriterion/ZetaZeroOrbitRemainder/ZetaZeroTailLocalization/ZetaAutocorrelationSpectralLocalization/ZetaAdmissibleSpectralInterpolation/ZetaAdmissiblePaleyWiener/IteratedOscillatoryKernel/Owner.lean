import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.OwnerParts.HighFrequency

/-!
# Paley-Wiener iterated oscillatory kernel assembly

This file keeps the low/high frequency assembly and Laplace-transform
integration-by-parts wrappers. The iterated high-frequency owner is split into
`OwnerParts.HighFrequency`.
-/

open scoped Real
open MeasureTheory
open scoped ContDiff

namespace Boundary
namespace LFunctions

open ZetaAdmissibleFunction

/-- Pointwise low/high frequency decision for the positive-order Fourier estimate. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_from_low_high_pointwise
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ)
    (Clow Chigh : ℝ)
    (hClow :
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖y‖ ≤ 1 →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ Clow * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
    (hChigh :
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
    (x y : ℝ) (hx_left : a ≤ x) (hx_right : x ≤ b) :
    ‖∫ t : ℝ,
      zetaPaleyWienerVerticalLineIBPDerivative f x t *
        zetaPaleyWienerVerticalOscillation y t‖
      ≤ max Clow Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
  let hweight :
      0 ≤ (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    zetaPaleyWiener_realVerticalDecayWeight_nonnegative y (Nat.succ N)
  if hlow_region : ‖y‖ ≤ 1 then
    let hbound :
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ Clow * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
      hClow x y hx_left hx_right hlow_region
    let hconstant :
        Clow * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) ≤
          max Clow Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_left Clow Chigh) hweight
    hbound.trans hconstant
  else
    let hhigh_region : 1 ≤ ‖y‖ :=
      le_of_lt (lt_of_not_ge hlow_region)
    let hbound :
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
      hChigh x y hx_left hx_right hhigh_region
    let hconstant :
        Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) ≤
          max Clow Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_right Clow Chigh) hweight
    hbound.trans hconstant

/-- The deterministic positive-order Fourier constant for the first derivative source,
combining the low-frequency compact bound and the high-frequency repeated-IBP constant. -/
noncomputable def zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) : ℝ :=
  max
    (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant
      f I a b N)
    (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
      f I a b 1 (Nat.succ N))

/-- The deterministic positive-order Fourier constant is positive. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant_pos
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    0 <
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant
        f I a b N :=
  lt_of_lt_of_le
    (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant_pos
      f I a b N)
    (le_max_left
      (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant
        f I a b N)
      (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
        f I a b 1 (Nat.succ N)))

/-- The deterministic positive-order Fourier constant bounds the first derivative
oscillatory integral on the full frequency line. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖
        ≤
          zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant
              f I a b N *
            (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
  let Clow : ℝ :=
    zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant
      f I a b N
  let Chigh : ℝ :=
    zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant
      f I a b 1 (Nat.succ N)
  let hClow :
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        ‖y‖ ≤ 1 →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ Clow * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderLowFrequencyConstant_bound
      f I a b N
  let hChigh :
      ∀ x y : ℝ,
        a ≤ x →
        x ≤ b →
        1 ≤ ‖y‖ →
        ‖∫ t : ℝ,
          zetaPaleyWienerVerticalLineIBPDerivative f x t *
            zetaPaleyWienerVerticalOscillation y t‖
          ≤ Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
    fun x y hxLeft hxRight hyHigh =>
      let hiter :
          ‖zetaPaleyWienerIteratedDerivativeOscillatoryIntegral f 1 x y‖
            ≤ Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)) :=
        zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_highFrequencyConstant_bound
          f I a b 1 (Nat.succ N) x y hxLeft hxRight hyHigh
      Eq.subst
        (motive := fun v : ℂ =>
          ‖v‖ ≤ Chigh * (1 + ‖y‖) ^ (-((Nat.succ N : ℕ) : ℤ)))
        (zetaPaleyWienerIteratedDerivativeOscillatoryIntegral_one f x y)
        hiter
  zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrder_from_low_high_pointwise
    f a b N Clow Chigh hClow hChigh

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
  exact
    ⟨zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant
        f I a b N,
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant_pos
        f I a b N,
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant_bound
        f I a b N⟩

/-- The deterministic all-orders Fourier constant for the first derivative source. -/
noncomputable def zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) : ℝ :=
  match N with
  | Nat.zero =>
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant
        f I a b
  | Nat.succ N =>
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant
        f I a b N

/-- The deterministic all-orders Fourier constant is positive. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_pos
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    0 <
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
        f I a b N := by
  cases N with
  | zero =>
      exact
        zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant_pos
          f I a b
  | succ N =>
      exact
        zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant_pos
          f I a b N

/-- The deterministic all-orders Fourier constant bounds the first derivative
oscillatory integral. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∀ x y : ℝ,
      a ≤ x →
      x ≤ b →
      ‖∫ t : ℝ,
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t‖
        ≤
          zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
              f I a b N *
            (1 + ‖y‖) ^ (-(N : ℤ)) := by
  cases N with
  | zero =>
      intro x y hxLeft hxRight
      let C : ℝ :=
        zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant
          f I a b
      let hraw :
          ‖∫ t : ℝ,
            zetaPaleyWienerVerticalLineIBPDerivative f x t *
              zetaPaleyWienerVerticalOscillation y t‖ ≤ C :=
        zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_zeroOrderConstant_bound
          f I a b x y hxLeft hxRight
      let hweight :
          C * (1 + ‖y‖) ^ (-(0 : ℤ)) = C :=
        Eq.trans
          (congrArg (fun v : ℝ => C * v) (zetaPaleyWiener_zeroDecayWeight y))
          (mul_one C)
      exact Eq.subst
        (motive := fun v : ℝ =>
          ‖∫ t : ℝ,
            zetaPaleyWienerVerticalLineIBPDerivative f x t *
              zetaPaleyWienerVerticalOscillation y t‖ ≤ v)
        hweight.symm
        hraw
  | succ N =>
      exact
        zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_positiveOrderConstant_bound
          f I a b N

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
  exact
    ⟨zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
        f I a b N,
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_pos
        f I a b N,
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_bound
        f I a b N⟩

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
  exact
    ⟨zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
        f I a b N,
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_pos
        f I a b N,
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_bound
        f I a b N⟩

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
  exact
    ⟨zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
        f I a b N,
      zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_pos
        f I a b N,
      fun z hz =>
        zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_bound
          f I a b N z.re z.im hz.1 hz.2⟩

/-- High-frequency Paley-Wiener control from vertical-line integration by parts on a compact
real-part strip.

The honest strip argument does not produce one derivative probe independent of `z`.  On the
vertical line `re z = x`, integration by parts differentiates the compactly supported source
after multiplying by the horizontal factor `Real.exp (x * t)`, and the constants are then made
uniform for `x ∈ [a,b]`.  This theorem owns that compact-strip vertical-line transport. -/
theorem zetaLaplaceTransform_supportInterval_successor_highFrequency_decay_from_verticalLineIBP
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      1 ≤ ‖z.im‖ →
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
        ≤
          (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
              f I a b N * 2) *
            zetaPaleyWienerVerticalWeight z (N + 1) := by
  let C : ℝ :=
    zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
      f I a b N
  have hC_pos : 0 < C :=
    zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_pos
      f I a b N
  exact fun z hzstrip hzhigh =>
        let hparts :
            ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
              ‖(z.im : ℂ)⁻¹‖ *
                ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ :=
          zetaLaplaceTransform_supportInterval_verticalLineIBP_normComparison
            f I a b z hzstrip hzhigh
        let hderivativeBound :
            ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖
              ≤ C * zetaPaleyWienerVerticalWeight z N :=
          zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant_bound
            f I a b N z.re z.im hzstrip.1 hzstrip.2
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
          (hrenorm.trans_eq htarget)))

/-- Pointwise low-frequency successor transport from an explicit current constant. -/
theorem zetaLaplaceTransform_supportInterval_successor_lowFrequency_bound
    (f : ZetaAdmissibleFunction)
    (a b : ℝ) (N : ℕ)
    (C : ℝ) (hC_pos : 0 < C)
    (hC :
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z N) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ‖z.im‖ ≤ 1 →
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
        ≤ (C * 2) * zetaPaleyWienerVerticalWeight z (N + 1) :=
  fun z hzstrip hzlow =>
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
    hbound.trans (hrenorm.trans_eq hreassociate)

/-- Pointwise low/high frequency decision for the global successor strip estimate. -/
theorem zetaLaplaceTransform_supportInterval_successor_decay_from_low_high_pointwise
    (f : ZetaAdmissibleFunction)
    (a b : ℝ) (N : ℕ)
    (Clow Chigh : ℝ)
    (hClow :
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖z.im‖ ≤ 1 →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ Clow * zetaPaleyWienerVerticalWeight z (N + 1))
    (hChigh :
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        1 ≤ ‖z.im‖ →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ Chigh * zetaPaleyWienerVerticalWeight z (N + 1))
    (z : ℂ) (hz : zetaPaleyWienerInVerticalStrip a b z) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
      ≤ max Clow Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
  let hweight : 0 ≤ zetaPaleyWienerVerticalWeight z (N + 1) :=
    zetaPaleyWienerVerticalWeight_nonnegative z (N + 1)
  if hlow_region : ‖z.im‖ ≤ 1 then
    let hbound :
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ Clow * zetaPaleyWienerVerticalWeight z (N + 1) :=
      hClow z hz hlow_region
    let hconstant :
        Clow * zetaPaleyWienerVerticalWeight z (N + 1) ≤
          max Clow Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left Clow Chigh) hweight
    hbound.trans hconstant
  else
    let hhigh_region : 1 ≤ ‖z.im‖ :=
      le_of_lt (lt_of_not_ge hlow_region)
    let hbound :
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
      hChigh z hz hhigh_region
    let hconstant :
        Chigh * zetaPaleyWienerVerticalWeight z (N + 1) ≤
          max Clow Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
      mul_le_mul_of_nonneg_right (le_max_right Clow Chigh) hweight
    hbound.trans hconstant

/-- The deterministic vertical-strip Laplace decay constant on a fixed support interval. -/
noncomputable def zetaLaplaceTransform_supportInterval_decayConstant
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) : ℝ :=
  match N with
  | Nat.zero =>
      zetaPaleyWienerZeroOrderEnvelope f I a b
  | Nat.succ N =>
      max
        (zetaLaplaceTransform_supportInterval_decayConstant f I a b N * 2)
        (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
          f I a b N * 2)

/-- The deterministic vertical-strip Laplace decay constant is positive. -/
theorem zetaLaplaceTransform_supportInterval_decayConstant_pos
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    0 < zetaLaplaceTransform_supportInterval_decayConstant f I a b N := by
  induction N with
  | zero =>
      exact zetaPaleyWienerZeroOrderEnvelope_pos f I a b
  | succ N ih =>
      exact lt_of_lt_of_le
        (mul_pos ih zero_lt_two)
        (le_max_left
          (zetaLaplaceTransform_supportInterval_decayConstant f I a b N * 2)
          (zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
            f I a b N * 2))

/-- The deterministic vertical-strip Laplace decay constant bounds the Laplace transform. -/
theorem zetaLaplaceTransform_supportInterval_decayConstant_bound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∀ z : ℂ,
      zetaPaleyWienerInVerticalStrip a b z →
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
        ≤ zetaLaplaceTransform_supportInterval_decayConstant f I a b N *
          zetaPaleyWienerVerticalWeight z N := by
  induction N with
  | zero =>
      intro z hz
      let C : ℝ := zetaPaleyWienerZeroOrderEnvelope f I a b
      let hraw :
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤ C :=
        zetaLaplaceTransform_supportInterval_zeroOrder_le_envelope f I a b z hz
      let hweight :
          C * zetaPaleyWienerVerticalWeight z 0 = C := by
        let hzero : zetaPaleyWienerVerticalWeight z 0 = 1 := by
          unfold zetaPaleyWienerVerticalWeight
          exact zpow_zero (1 + ‖z.im‖)
        exact Eq.trans (congrArg (fun W : ℝ => C * W) hzero) (mul_one C)
      exact Eq.subst
        (motive := fun v : ℝ =>
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤ v)
        hweight.symm
        hraw
  | succ N ih =>
      intro z hz
      let Clow : ℝ :=
        zetaLaplaceTransform_supportInterval_decayConstant f I a b N * 2
      let Chigh : ℝ :=
        zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
          f I a b N * 2
      let hlow :
          ∀ z : ℂ,
            zetaPaleyWienerInVerticalStrip a b z →
            ‖z.im‖ ≤ 1 →
            ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
              ≤ Clow * zetaPaleyWienerVerticalWeight z (N + 1) :=
        zetaLaplaceTransform_supportInterval_successor_lowFrequency_bound
          f a b N
          (zetaLaplaceTransform_supportInterval_decayConstant f I a b N)
          (zetaLaplaceTransform_supportInterval_decayConstant_pos f I a b N)
          ih
      let hhigh :
          ∀ z : ℂ,
            zetaPaleyWienerInVerticalStrip a b z →
            1 ≤ ‖z.im‖ →
            ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
              ≤ Chigh * zetaPaleyWienerVerticalWeight z (N + 1) :=
        fun z hzstrip hzhigh =>
          let Cder : ℝ :=
            zetaPaleyWienerHorizontalTwistDerivative_fourierIntegral_uniformConstant
              f I a b N
          let hstep :
              ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
                ≤ (Cder * 2) * zetaPaleyWienerVerticalWeight z (N + 1) :=
            zetaLaplaceTransform_supportInterval_successor_highFrequency_decay_from_verticalLineIBP
              f I a b N z hzstrip hzhigh
          hstep
      exact
        zetaLaplaceTransform_supportInterval_successor_decay_from_low_high_pointwise
          f a b N Clow Chigh hlow hhigh z hz

/-- One integration-by-parts step for Paley-Wiener control on a fixed compact support
interval.

The step consumes the `N`th vertical decay estimate and produces the successor estimate by
integrating by parts once more; smoothness bounds the next derivative seminorm and compact
support kills the boundary terms. -/
theorem zetaLaplaceTransform_supportInterval_integrationByParts_successor
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        zetaPaleyWienerInVerticalStrip a b z →
        ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
          ≤ C * zetaPaleyWienerVerticalWeight z (N + 1) := by
  exact
    ⟨zetaLaplaceTransform_supportInterval_decayConstant f I a b (N + 1),
      zetaLaplaceTransform_supportInterval_decayConstant_pos f I a b (N + 1),
      zetaLaplaceTransform_supportInterval_decayConstant_bound f I a b (N + 1)⟩

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
  intro f I a b
  exact
    ⟨zetaLaplaceTransform_supportInterval_decayConstant f I a b N,
      zetaLaplaceTransform_supportInterval_decayConstant_pos f I a b N,
      zetaLaplaceTransform_supportInterval_decayConstant_bound f I a b N⟩

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
  exact
    ⟨zetaLaplaceTransform_supportInterval_decayConstant f I a b N,
      zetaLaplaceTransform_supportInterval_decayConstant_pos f I a b N,
      zetaLaplaceTransform_supportInterval_decayConstant_bound f I a b N⟩

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
  exact zetaLaplaceTransform_verticalStripDecayConstant_of_supportInterval_integrationByParts
    f (canonicalZetaPaleyWienerSupportInterval f) a b N

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
  let I : ZetaPaleyWienerSupportInterval f :=
    canonicalZetaPaleyWienerSupportInterval f
  let C : ℝ :=
    zetaLaplaceTransform_supportInterval_decayConstant f I a b N
  exact ⟨C,
    zetaLaplaceTransform_supportInterval_decayConstant_pos f I a b N,
    fun z haz hzb =>
      zetaLaplaceTransform_supportInterval_decayConstant_bound
        f I a b N z ⟨haz, hzb⟩⟩

end LFunctions
end Boundary
