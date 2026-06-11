import Boundary.LFunctions.ZetaExplicitFormulaContour
import Boundary.LFunctions.ZetaExplicitFormulaContourBounds
import Boundary.LFunctions.ZetaExplicitFormulaHorizontalEdgeBounds
import Boundary.LFunctions.ZetaExplicitFormulaResidueRegularity
import Boundary.LFunctions.ZetaExplicitFormulaNormalizationBridge
import Boundary.LFunctions.ZetaExplicitFormulaGeometry
import Boundary.LFunctions.ZetaExplicitFormulaAnalyticPackage
import Boundary.LFunctions.ZetaCompletedLogDerivativeCore
import Boundary.LFunctions.ZetaExplicitFormulaLogDerivative
import Boundary.LFunctions.ZetaAdmissibleTransformRegularity
import Boundary.LFunctions.ZetaCompletedLogDerivativeControl
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Boundary explicit-formula complex analysis API

This file exposes the geometric and analytic objects needed for the completed
Guinand--Weil contour argument. It intentionally stops at definitions and
owner-level notation; the actual contour estimates will be proved against these
objects in later files.

The point is to make the required complex-analysis API available first, not to
axiomatize the missing theorems.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A boundary-side interval-integral norm estimate. This is the reusable lemma the
horizontal contour argument needs: the norm of an interval integral is controlled via the
interval integral of the pointwise norm. -/
theorem norm_intervalIntegral_le_integral_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E)
    (a b : ℂ) (hab : a.re ≤ b.re) :
    ‖∫ x in a.re..b.re, f (x + a.im * Complex.I)‖
      ≤ ∫ x in a.re..b.re, ‖f (x + a.im * Complex.I)‖ :=
  intervalIntegral.norm_integral_le_integral_norm
    (f := fun x : ℝ => f (x + a.im * Complex.I)) hab

/-- A horizontal line integral is controlled from a pointwise constant bound on the integrand. -/
theorem horizontalLineIntegral_norm_le_constant
    (g : ℝ → ℂ) (a b C : ℝ)
    (hab : a ≤ b)
    (hg : ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ C) :
    ‖∫ x in a..b, g x‖ ≤ (b - a) * C :=
  intervalIntegral_norm_le_oriented_constant g a b C hab hg

/-- The interval-integral estimate packaged with the contour-family top path. -/
theorem horizontalTopLineIntegral_norm_le_constant
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (T : ℝ) :
    ‖∫ x in Set.uIcc F.c (1 - F.c),
        zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstant
          h.phi_control h.logderiv_control (F.rectangle T) N *
        horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaTopLineIntegral_uIcc_norm_le_envelope
      h.phi_control h.logderiv_control (F.rectangle T) N

/-- The interval-integral estimate packaged with the contour-family bottom path. -/
theorem horizontalBottomLineIntegral_norm_le_constant
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (T : ℝ) :
    ‖∫ x in Set.uIcc F.c (1 - F.c),
        zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstant
          h.phi_control h.logderiv_control (F.rectangle T) N *
        horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaBottomLineIntegral_uIcc_norm_le_envelope
      h.phi_control h.logderiv_control (F.rectangle T) N

/-- A horizontal line integral along a contour family is bounded by the explicit edge constant.
This packages the pointwise contour estimate with the interval-length estimate in one place. -/
theorem horizontalLineIntegral_norm_le_contourBound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (T : ℝ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ ≤
      horizontalUnorderedEdgeIntegrandBoundConstant
          h.phi_control h.logderiv_control (F.rectangle T) N *
        horizontalEdgeLength F.c :=
  horizontalTopLineIntegral_norm_le_constant h N T

/-- The bottom horizontal line integral is bounded by the explicit edge constant. -/
theorem horizontalLineIntegral_norm_le_contourBound_bottom
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (T : ℝ) :
    ‖zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖ ≤
      horizontalUnorderedEdgeIntegrandBoundConstant
          h.phi_control h.logderiv_control (F.rectangle T) N *
        horizontalEdgeLength F.c :=
  horizontalBottomLineIntegral_norm_le_constant h N T

/-- A lower bound for `T` gives the same lower bound for `1 + ‖T‖`. -/
theorem le_one_add_norm_of_le_self {a T : ℝ} (hT : a ≤ T) :
    a ≤ 1 + ‖T‖ :=
  le_trans hT
    (le_trans (Real.le_norm_self T) (le_add_of_nonneg_left zero_le_one))

/-- The function `T ↦ 1 + ‖T‖` tends to infinity at `atTop`. -/
theorem tendsto_one_add_norm_atTop :
    Tendsto (fun T : ℝ => (1 + ‖T‖ : ℝ)) atTop atTop :=
  tendsto_atTop.2
    (fun a =>
      (eventually_ge_atTop a).mono
        (fun T hT => le_one_add_norm_of_le_self hT))

/-- Positive natural powers of `1 + |T|` tend to infinity at `atTop`. -/
theorem tendsto_one_add_norm_natPow_succ_atTop (N : ℕ) :
    Tendsto (fun T : ℝ => (1 + ‖T‖ : ℝ) ^ (N.succ : ℕ)) atTop atTop :=
  (tendsto_pow_atTop (Nat.succ_ne_zero N)).comp tendsto_one_add_norm_atTop

/-- Powers of `1 + |T|` with negative positive exponent tend to zero at `atTop`. -/
theorem tendsto_one_add_norm_pow_neg_atTop (N : ℕ) :
    Tendsto (fun T : ℝ => (1 + ‖T‖) ^ (-(N.succ : ℤ))) atTop (𝓝 (0 : ℝ)) :=
  (tendsto_zpow_atTop_zero (Int.negSucc_lt_zero N)).comp tendsto_one_add_norm_atTop

/-- If a real-valued function is dominated by a constant multiple of a quantity tending to `0`,
then it tends to `0`. -/
theorem tendsto_of_eventually_le_mul_tendsto_zero
    {g h : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hg : ∀ᶠ T in atTop, ‖g T‖ ≤ C * h T)
    (hh : Tendsto h atTop (𝓝 (0 : ℝ))) :
    Tendsto g atTop (𝓝 (0 : ℝ)) := by
  have hmul : Tendsto (fun T : ℝ => C * h T) atTop (𝓝 (0 : ℝ)) := by
    exact Eq.subst
      (motive := fun y : ℝ => Tendsto (fun T : ℝ => C * h T) atTop (𝓝 y))
      (mul_zero C)
      (hh.const_mul C)
  exact squeeze_zero_norm' hg hmul

/-- The product of two negative powers of `1 + |T|` tends to zero. -/
theorem tendsto_two_one_add_norm_pow_neg_atTop (N : ℕ) :
    Tendsto
      (fun T : ℝ => (1 + ‖T‖) ^ (-(N.succ : ℤ)) * (1 + ‖T‖) ^ (-(N.succ : ℤ)))
      atTop
      (𝓝 (0 : ℝ)) :=
  Eq.subst
    (motive := fun y : ℝ =>
      Tendsto
        (fun T : ℝ => (1 + ‖T‖) ^ (-(N.succ : ℤ)) * (1 + ‖T‖) ^ (-(N.succ : ℤ)))
        atTop
        (𝓝 y))
    (mul_zero (0 : ℝ))
    ((tendsto_one_add_norm_pow_neg_atTop N).mul
      (tendsto_one_add_norm_pow_neg_atTop N))

/-- The single-rectangle top horizontal integral is bounded by the unordered edge constant. -/
theorem horizontalIntegral_norm_le_uniformContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (N : ℕ)
    :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaTopLineIntegral f h.contour_data.rectangle‖ ≤ C :=
  ⟨horizontalUnorderedEdgeIntegrandBoundConstant
      h.phi_control h.logderiv_control h.contour_data.rectangle N *
      horizontalEdgeLength h.contour_data.rectangle.c,
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x))
      h.contour_data.rectangle.c
      (horizontalUnorderedEdgeIntegrandBoundConstant
        h.phi_control h.logderiv_control h.contour_data.rectangle N)
      (fun x hx =>
        zetaCompletedExplicitFormulaTopEdgeContourIntegrand_uIcc_bound
          h.phi_control h.logderiv_control h.contour_data.rectangle x hx N)⟩

/-- The single-rectangle bottom horizontal integral is bounded by the unordered edge constant. -/
theorem horizontalBottomIntegral_norm_le_uniformContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (N : ℕ) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaBottomLineIntegral f h.contour_data.rectangle‖ ≤ C :=
  ⟨horizontalUnorderedEdgeIntegrandBoundConstant
      h.phi_control h.logderiv_control h.contour_data.rectangle N *
      horizontalEdgeLength h.contour_data.rectangle.c,
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x))
      h.contour_data.rectangle.c
      (horizontalUnorderedEdgeIntegrandBoundConstant
        h.phi_control h.logderiv_control h.contour_data.rectangle N)
      (fun x hx =>
        zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_uIcc_bound
          h.phi_control h.logderiv_control h.contour_data.rectangle x hx N)⟩

/-- A norm bound for a difference follows from separate bounds on its two terms. -/
theorem norm_sub_le_add_of_norm_bounds {a b : ℂ} {A B : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖a - b‖ ≤ A + B :=
  (norm_sub_le a b).trans (add_le_add ha hb)

/-- The horizontal difference of the top and bottom integrals is bounded by twice the uniform
edge constant times the interval length. -/
theorem horizontalDifference_norm_le_uniformContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (N : ℕ) :
    ∃ C : ℝ,
      ‖zetaHorizontalIntegralTop f h.contour_data.rectangle -
        zetaHorizontalIntegralBottom f h.contour_data.rectangle‖ ≤ C := by
  match horizontalIntegral_norm_le_uniformContourBound h N,
      horizontalBottomIntegral_norm_le_uniformContourBound h N with
  | ⟨Ctop, htop⟩, ⟨Cbot, hbot⟩ =>
      exact ⟨Ctop + Cbot, norm_sub_le_add_of_norm_bounds htop hbot⟩

/-- The top horizontal line integral in a contour family is bounded by the uniform family edge
bound times the horizontal length. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topLineIntegral_norm_le_core
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (T : ℝ) :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ ≤ C :=
  ⟨horizontalUnorderedEdgeIntegrandBoundConstant
      h.phi_control h.logderiv_control (F.rectangle T) N *
      horizontalEdgeLength F.c,
    horizontalLineIntegral_norm_le_contourBound h N T⟩

/-- Thin wrapper for the top horizontal line integral estimate. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topLineIntegral_norm_le
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (T : ℝ) :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ ≤ C :=
  h.topLineIntegral_norm_le_core N T

/-- The shared decay envelope controlling the horizontal family estimates. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecayEnvelope_core
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) :
    ∃ C : ℝ,
      Tendsto
        (fun T : ℝ =>
          C * (1 + ‖T‖) ^ (-(N.succ : ℤ)) * (1 + ‖T‖) ^ (-(N.succ : ℤ)))
        atTop (𝓝 (0 : ℝ)) := by
  have hprod := tendsto_two_one_add_norm_pow_neg_atTop N
  refine ⟨horizontalEdgeLength F.c *
      h.logderiv_control.stripBoundConstant F.c (1 - F.c) N *
      h.phi_control.verticalStripRapidDecayConstant (F.c - 1 / 2) (1 / 2 - F.c) N, ?_⟩
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    hprod.const_mul (horizontalEdgeLength F.c *
      h.logderiv_control.stripBoundConstant F.c (1 - F.c) N *
      h.phi_control.verticalStripRapidDecayConstant (F.c - 1 / 2) (1 / 2 - F.c) N)

/-- Thin wrapper for the horizontal decay envelope. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecayEnvelope
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) :
    ∃ C : ℝ,
      Tendsto
        (fun T : ℝ =>
          C * (1 + ‖T‖) ^ (-(N.succ : ℤ)) * (1 + ‖T‖) ^ (-(N.succ : ℤ)))
        atTop (𝓝 (0 : ℝ)) :=
  h.horizontalDecayEnvelope_core N

/-- The horizontal top-minus-bottom difference tends to zero along a contour family. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecay_core
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      atTop
      (𝓝 (0 : ℝ)) :=
  zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero
    h.phi_control h.logderiv_control F N

/-- Thin wrapper for the horizontal decay of the top-minus-bottom difference. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecay
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      atTop
      (𝓝 (0 : ℝ)) :=
  h.horizontalDecay_core N

/-- A reusable bound for the bottom horizontal line integral in terms of pointwise edge bounds. -/
theorem ExplicitFormulaFamilyAnalyticPackage.bottomLineIntegral_norm_le_core
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) (T : ℝ) :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖ ≤ C :=
  ⟨horizontalUnorderedEdgeIntegrandBoundConstant
      h.phi_control h.logderiv_control (F.rectangle T) N *
      horizontalEdgeLength F.c,
    horizontalLineIntegral_norm_le_contourBound_bottom h N T⟩



/-- The analytic package exposes the owner-level reflected-autocorrelation identity. -/
theorem zetaCompletedExplicitFormulaContourBoundary_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.autocorrelation (ZetaAdmissibleFunction.reflect f) =
      ZetaAdmissibleFunction.reflect (ZetaAdmissibleFunction.autocorrelation f) :=
  ZetaAdmissibleFunction.autocorrelation_dagger_eq_reflect f

/-- The rectangle theorem applies to the factorized contour integrand once its analytic hypotheses
are provided. -/
theorem zetaCompletedExplicitFormulaRectangleBoundaryIdentity_factorized
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (f' : ℂ → (ℂ →L[ℝ] ℂ))
    (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn (fun z : ℂ =>
      (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im))
    (Hd : ∀ x, x ∈ Set.Ioo (min (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re)
        (max (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re) ×ℂ
        Set.Ioo (min (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im)
          (max (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) \ s →
        HasFDerivAt
          (fun z : ℂ =>
            (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
          (f' x) x)
    (Hi : IntegrableOn
      (fun z => Complex.I • ⇑(f' z) 1 - ⇑(f' z) Complex.I)
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) volume) :
    (((∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
            (x + (r.c + (-r.T) * Complex.I).im * Complex.I)) *
            zetaCompletedExplicitFormulaPhi f
              (x + (r.c + (-r.T) * Complex.I).im * Complex.I - 1 / 2)) -
        ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
            (x + (r.c + (r.T) * Complex.I).im * Complex.I)) *
            zetaCompletedExplicitFormulaPhi f
              (x + (r.c + (r.T) * Complex.I).im * Complex.I - 1 / 2)) +
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
          ((r.c + (r.T) * Complex.I).re + y * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            ((r.c + (r.T) * Complex.I).re + y * Complex.I - 1 / 2)) -
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
          ((r.c + (-r.T) * Complex.I).re + y * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            ((r.c + (-r.T) * Complex.I).re + y * Complex.I - 1 / 2)
      =
      ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
        ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
          Complex.I • ⇑(f' (x + y * Complex.I)) 1 - ⇑(f' (x + y * Complex.I)) Complex.I :=
  Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable
    (f := fun z : ℂ =>
      (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
    (f' := f') (z := r.c + (-r.T) * Complex.I) (w := r.c + (r.T) * Complex.I)
    (s := s) (hs := hs) (Hc := Hc) (Hd := Hd) (Hi := Hi)


/-- The boundary sum splits into prime, archimedean, and correction pieces. -/
theorem zetaCompletedExplicitFormulaBoundaryPieces_bridge
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryPieces f =
      (zetaCompletedExplicitFormulaPrimeContribution f,
        zetaCompletedExplicitFormulaArchimedeanContribution f,
        zetaCompletedExplicitFormulaCorrectionContribution f) :=
  rfl

/-- The analytic boundary sum is the sum of the three pieces. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_bridge
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionContribution f :=
  rfl

/-- The completed zeta contour integrand is compatible with the rectangle theorem
surface once differentiability hypotheses are supplied. -/
theorem zetaCompletedExplicitFormulaRectangleBoundaryIdentity
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (f' : ℂ → (ℂ →L[ℝ] ℂ))
    (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im))
    (Hd : ∀ x, x ∈ Set.Ioo (min (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re)
        (max (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re) ×ℂ
        Set.Ioo (min (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im)
          (max (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) \ s →
        HasFDerivAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) (f' x) x)
    (Hi : IntegrableOn
      (fun z => Complex.I • ⇑(f' z) 1 - ⇑(f' z) Complex.I)
      (Set.uIcc (r.c + (-r.T) * Complex.I).re (r.c + (r.T) * Complex.I).re ×ℂ
        Set.uIcc (r.c + (-r.T) * Complex.I).im (r.c + (r.T) * Complex.I).im) volume) :
    (((∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (r.c + (-r.T) * Complex.I).im * Complex.I)) -
        ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (r.c + (r.T) * Complex.I).im * Complex.I)) +
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        zetaCompletedExplicitFormulaContourIntegrand f
          ((r.c + (r.T) * Complex.I).re + y * Complex.I)) -
      Complex.I • ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
        zetaCompletedExplicitFormulaContourIntegrand f
          ((r.c + (-r.T) * Complex.I).re + y * Complex.I)
      =
      ∫ x in (r.c + (-r.T) * Complex.I).re..(r.c + (r.T) * Complex.I).re,
        ∫ y in (r.c + (-r.T) * Complex.I).im..(r.c + (r.T) * Complex.I).im,
          Complex.I • ⇑(f' (x + y * Complex.I)) 1 - ⇑(f' (x + y * Complex.I)) Complex.I :=
  Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable
    (f := fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
    (f' := f') (z := r.c + (-r.T) * Complex.I) (w := r.c + (r.T) * Complex.I)
    (s := s) (hs := hs) (Hc := Hc) (Hd := Hd) (Hi := Hi)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
