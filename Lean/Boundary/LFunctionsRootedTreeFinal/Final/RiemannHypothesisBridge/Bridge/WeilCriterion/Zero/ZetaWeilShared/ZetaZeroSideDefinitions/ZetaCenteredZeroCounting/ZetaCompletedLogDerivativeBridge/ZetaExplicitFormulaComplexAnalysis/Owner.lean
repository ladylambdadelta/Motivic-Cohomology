import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContourBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaResidueRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaNormalizationBridge.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.ZetaCompletedLogDerivativeCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaLogDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.Owner
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

The point is to make the required complex-analysis API available first, with
the contour estimates proved in their owner files.
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
    Tendsto
      (fun T : ℝ =>
        horizontalUnorderedFamilyDifferenceEnvelopeSplit
          h.phi_control h.logderiv_control F N (N + N.succ) T)
      atTop (𝓝 (0 : ℝ)) := by
  exact horizontalUnorderedFamilyDifferenceEnvelopeSplit_tendsto_zero
    h.phi_control h.logderiv_control F N N

/-- Thin wrapper for the horizontal decay envelope. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecayEnvelope
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalUnorderedFamilyDifferenceEnvelopeSplit
          h.phi_control h.logderiv_control F N (N + N.succ) T)
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
      (𝓝 (0 : ℂ)) :=
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
      (𝓝 (0 : ℂ)) :=
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

/-- The residue-window error left after subtracting the finite completed-zero window from the
rectangle contour integral. -/
noncomputable def explicitFormulaFamilyResidueWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
    explicitFormulaCompletedZeroHeightWindowResidueSum f T

/-- The finite-rectangle vertical residue-window error: the right-minus-left vertical
contour contribution after subtracting the finite completed-zero residue window. -/
noncomputable def explicitFormulaFamilyVerticalResidueWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) -
      explicitFormulaCompletedZeroHeightWindowResidueSum f T

/-- The vertical finite-window error written using the zero-side finite window rather than
the residue presentation. -/
noncomputable def explicitFormulaFamilyVerticalZeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) -
      explicitFormulaCompletedZeroHeightWindowZeroSideSum f T

/-- The full finite-rectangle residue-theorem error after replacing the residue window by
the zero-side finite window. -/
noncomputable def explicitFormulaFamilyContourZeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
    explicitFormulaCompletedZeroHeightWindowZeroSideSum f T

/-- The scheduled finite-rectangle residue sum before zero-side accounting.  The supplied
cofinal schedule provides the heights used by the finite residue theorem, which computes the
contour integral against this residue-window presentation. -/
noncomputable def explicitFormulaScheduledRectangleResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  explicitFormulaCompletedZeroHeightWindowResidueSum f (h.height_schedule.height u)

/-- The scheduled finite-rectangle residue equality error: contour integral minus the finite
residue sum obtained from the residue theorem at the scheduled height. -/
noncomputable def explicitFormulaScheduledRectangleResidueEqualityError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f
      (F.rectangle (h.height_schedule.height u)) -
    explicitFormulaScheduledRectangleResidueSum f F h u

/-- The finite zero-window accounting error between the scheduled residue presentation and
the zero-side presentation. -/
noncomputable def explicitFormulaScheduledZeroWindowAccountingError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  explicitFormulaScheduledRectangleResidueSum f F h u -
    explicitFormulaCompletedZeroHeightWindowZeroSideSum f
      (h.height_schedule.height u)

/-- The horizontal residue-window error is the top-minus-bottom horizontal contour
contribution. -/
noncomputable def explicitFormulaFamilyHorizontalResidueWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)

/-- The rectangle contour integral is its finite completed-zero residue window plus the
residue-window error. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_heightWindowResidueSum_add_error
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T +
        explicitFormulaFamilyResidueWindowError f F T := by
  let C : ℂ := zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)
  let S : ℂ := explicitFormulaCompletedZeroHeightWindowResidueSum f T
  unfold explicitFormulaFamilyResidueWindowError
  change C = S + (C - S)
  calc
    C = C + 0 := by
      exact (add_zero C).symm
    _ = C + (-S + S) := by
      exact congrArg (fun x : ℂ => C + x) (neg_add_cancel S).symm
    _ = (C + -S) + S := by
      exact (add_assoc C (-S) S).symm
    _ = S + (C + -S) := by
      exact add_comm (C + -S) S
    _ = S + (C - S) := by
      exact congrArg (fun x : ℂ => S + x) (sub_eq_add_neg C S).symm

/-- The full residue-window error is the sum of the vertical finite-residue error and the
horizontal top-minus-bottom error. -/
theorem explicitFormulaFamilyResidueWindowError_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyResidueWindowError f F T =
      explicitFormulaFamilyVerticalResidueWindowError f F T +
        explicitFormulaFamilyHorizontalResidueWindowError f F T := by
  let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T)
  let L : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  let U : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)
  let B : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)
  let S : ℂ := explicitFormulaCompletedZeroHeightWindowResidueSum f T
  unfold explicitFormulaFamilyResidueWindowError
  unfold explicitFormulaFamilyVerticalResidueWindowError
  unfold explicitFormulaFamilyHorizontalResidueWindowError
  unfold zetaCompletedExplicitFormulaContourIntegral
  change (R - L + U - B) - S = (R - L - S) + (U - B)
  calc
    (R - L + U - B) - S = ((R - L) + U - B) - S := by
      rfl
    _ = (((R - L) + U) - B) - S := by
      rfl
    _ = (((R - L) + U) + -B) + -S := by
      exact sub_eq_add_neg (((R - L) + U) - B) S
    _ = ((R - L) + U + -B) + -S := by
      rfl
    _ = (R - L) + (U + -B) + -S := by
      exact congrArg (fun x : ℂ => x + -S) (add_assoc (R - L) U (-B))
    _ = (R - L) + (U - B) + -S := by
      exact congrArg (fun x : ℂ => (R - L) + x + -S) (sub_eq_add_neg U B).symm
    _ = (R - L) + ((U - B) + -S) := by
      exact add_assoc (R - L) (U - B) (-S)
    _ = (R - L) + (-S + (U - B)) := by
      exact congrArg (fun x : ℂ => (R - L) + x) (add_comm (U - B) (-S))
    _ = ((R - L) + -S) + (U - B) := by
      exact (add_assoc (R - L) (-S) (U - B)).symm
    _ = (R - L - S) + (U - B) := by
      exact congrArg (fun x : ℂ => x + (U - B)) (sub_eq_add_neg (R - L) S).symm

/-- The horizontal residue-window error is exactly the horizontal difference controlled by
the family horizontal-decay theorem. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyHorizontalResidueWindowError f F T)
      atTop
      (𝓝 0) := by
  exact h.horizontalDecay N

/-- The horizontal residue-window error also vanishes along the cofinal avoiding schedule. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (N : ℕ) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) :=
  (explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero f F h N).comp
    h.height_schedule.cofinal

/-- The residue-presentation and zero-side-presentation vertical finite-window errors agree. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_eq_zeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyVerticalResidueWindowError f F T =
      explicitFormulaFamilyVerticalZeroSideWindowError f F T := by
  let V : ℂ :=
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  have hwindow :
      explicitFormulaCompletedZeroHeightWindowResidueSum f T =
        explicitFormulaCompletedZeroHeightWindowZeroSideSum f T :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_eq_zeroSideSum f T
  unfold explicitFormulaFamilyVerticalResidueWindowError
  unfold explicitFormulaFamilyVerticalZeroSideWindowError
  change V - explicitFormulaCompletedZeroHeightWindowResidueSum f T =
    V - explicitFormulaCompletedZeroHeightWindowZeroSideSum f T
  exact congrArg (fun S : ℂ => V - S) hwindow

/-- If the zero-side presentation of the vertical finite-window error vanishes, then so does
the residue presentation. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_of_zeroSideWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hzeroSide :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalZeroSideWindowError f F T)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalResidueWindowError f F T)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyVerticalResidueWindowError f F T) =
        (fun T : ℝ => explicitFormulaFamilyVerticalZeroSideWindowError f F T) := by
    funext T
    exact explicitFormulaFamilyVerticalResidueWindowError_eq_zeroSideWindowError f F T
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hzeroSide

/-- Replacing the residue window by the zero-side window in the full contour error is only
the finite zero-window accounting identity. -/
theorem explicitFormulaFamilyContourZeroSideWindowError_eq_residueWindowError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyContourZeroSideWindowError f F T =
      explicitFormulaFamilyResidueWindowError f F T := by
  let C : ℂ := zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)
  have hwindow :
      explicitFormulaCompletedZeroHeightWindowResidueSum f T =
        explicitFormulaCompletedZeroHeightWindowZeroSideSum f T :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_eq_zeroSideSum f T
  unfold explicitFormulaFamilyContourZeroSideWindowError
  unfold explicitFormulaFamilyResidueWindowError
  change C - explicitFormulaCompletedZeroHeightWindowZeroSideSum f T =
    C - explicitFormulaCompletedZeroHeightWindowResidueSum f T
  exact congrArg (fun S : ℂ => C - S) hwindow.symm

/-- The scheduled zero-window accounting error vanishes pointwise: the finite rectangle
residue presentation is the zero-side finite window after the completed-zero residue
identification. -/
theorem explicitFormulaScheduledZeroWindowAccountingError_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledZeroWindowAccountingError f F h u = 0 := by
  unfold explicitFormulaScheduledZeroWindowAccountingError
  unfold explicitFormulaScheduledRectangleResidueSum
  have hwindow :
      explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u) =
        explicitFormulaCompletedZeroHeightWindowZeroSideSum f
          (h.height_schedule.height u) :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_eq_zeroSideSum
      f (h.height_schedule.height u)
  exact sub_eq_zero.mpr hwindow

/-- The scheduled zero-window accounting error tends to zero. -/
theorem explicitFormulaScheduledZeroWindowAccountingError_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ => explicitFormulaScheduledZeroWindowAccountingError f F h u)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ => explicitFormulaScheduledZeroWindowAccountingError f F h u) =
        (fun _u : ℝ => (0 : ℂ)) := by
    funext u
    exact explicitFormulaScheduledZeroWindowAccountingError_eq_zero f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    tendsto_const_nhds

/-- The scheduled contour zero-side error splits into the finite scheduled rectangle residue
equality error plus the finite zero-window accounting error. -/
theorem explicitFormulaFamilyContourZeroSideWindowError_scheduled_eq_residueEquality_add_accounting
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaFamilyContourZeroSideWindowError f F
        (h.height_schedule.height u) =
      explicitFormulaScheduledRectangleResidueEqualityError f F h u +
        explicitFormulaScheduledZeroWindowAccountingError f F h u := by
  let C : ℂ :=
    zetaCompletedExplicitFormulaContourIntegral f
      (F.rectangle (h.height_schedule.height u))
  let R : ℂ := explicitFormulaScheduledRectangleResidueSum f F h u
  let Z : ℂ :=
    explicitFormulaCompletedZeroHeightWindowZeroSideSum f
      (h.height_schedule.height u)
  unfold explicitFormulaFamilyContourZeroSideWindowError
  unfold explicitFormulaScheduledRectangleResidueEqualityError
  unfold explicitFormulaScheduledZeroWindowAccountingError
  change C - Z = (C - R) + (R - Z)
  calc
    C - Z = C + -Z := by
      exact sub_eq_add_neg C Z
    _ = C + (0 + -Z) := by
      exact congrArg (fun x : ℂ => C + (x + -Z)) (zero_add (0 : ℂ)).symm
    _ = C + ((-R + R) + -Z) := by
      exact congrArg (fun x : ℂ => C + (x + -Z)) (neg_add_cancel R).symm
    _ = C + (-R + (R + -Z)) := by
      exact congrArg (fun x : ℂ => C + x) (add_assoc (-R) R (-Z))
    _ = (C + -R) + (R + -Z) := by
      exact (add_assoc C (-R) (R + -Z)).symm
    _ = (C - R) + (R + -Z) := by
      exact congrArg (fun x : ℂ => x + (R + -Z)) (sub_eq_add_neg C R).symm
    _ = (C - R) + (R - Z) := by
      exact congrArg (fun x : ℂ => (C - R) + x) (sub_eq_add_neg R Z).symm

/-- The vertical zero-side window error is the full finite-rectangle residue-theorem error
with the horizontal side contribution subtracted. -/
theorem explicitFormulaFamilyVerticalZeroSideWindowError_eq_contourZeroSide_sub_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyVerticalZeroSideWindowError f F T =
      explicitFormulaFamilyContourZeroSideWindowError f F T -
        explicitFormulaFamilyHorizontalResidueWindowError f F T := by
  let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T)
  let L : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  let U : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)
  let B : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)
  let S : ℂ := explicitFormulaCompletedZeroHeightWindowZeroSideSum f T
  unfold explicitFormulaFamilyVerticalZeroSideWindowError
  unfold explicitFormulaFamilyContourZeroSideWindowError
  unfold explicitFormulaFamilyHorizontalResidueWindowError
  unfold zetaCompletedExplicitFormulaContourIntegral
  change R - L - S = ((R - L + U - B) - S) - (U - B)
  calc
    ((R - L + U - B) - S) - (U - B)
        = (((R - L) + U - B) - S) - (U - B) := by
      rfl
    _ = ((((R - L) + U) - B) - S) - (U - B) := by
      rfl
    _ = ((((R - L) + U) + -B) + -S) + -(U - B) := by
      exact sub_eq_add_neg ((((R - L) + U) - B) - S) (U - B)
    _ = (((R - L) + U + -B) + -S) + -(U - B) := by
      rfl
    _ = (((R - L) + (U + -B)) + -S) + -(U - B) := by
      exact congrArg (fun x : ℂ => (x + -S) + -(U - B))
        (add_assoc (R - L) U (-B))
    _ = (((R - L) + (U - B)) + -S) + -(U - B) := by
      exact congrArg (fun x : ℂ => (((R - L) + x) + -S) + -(U - B))
        (sub_eq_add_neg U B).symm
    _ = ((R - L) + ((U - B) + -S)) + -(U - B) := by
      exact congrArg (fun x : ℂ => x + -(U - B))
        (add_assoc (R - L) (U - B) (-S))
    _ = ((R - L) + (-S + (U - B))) + -(U - B) := by
      exact congrArg (fun x : ℂ => ((R - L) + x) + -(U - B))
        (add_comm (U - B) (-S))
    _ = (((R - L) + -S) + (U - B)) + -(U - B) := by
      exact congrArg (fun x : ℂ => x + -(U - B))
        (add_assoc (R - L) (-S) (U - B)).symm
    _ = ((R - L) + -S) + ((U - B) + -(U - B)) := by
      exact add_assoc ((R - L) + -S) (U - B) (-(U - B))
    _ = ((R - L) + -S) + 0 := by
      exact congrArg (fun x : ℂ => ((R - L) + -S) + x) (add_neg_cancel (U - B))
    _ = (R - L) + -S := by
      exact add_zero ((R - L) + -S)
    _ = R - L - S := by
      exact (sub_eq_add_neg (R - L) S).symm

/-- Owner complex zero-limit theorem for the finite completed-zero residue windows.

This is the zero-side summability/Jensen input specialized to the residue windows:
the finite height-window residue sums converge to the completed complex zero-side residue
sum.  Passing to the Krein scalar is a real-part operation, not a complex equality with a
coerced real number. -/
theorem explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hzeroSideTsum :
      Tendsto
        (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
        atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
            zetaZeroSideContribution (ρ : ℂ) f)) :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideTsum f hsum
  have hzeroSideTsum_eq_complex :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          zetaZeroSideContribution (ρ : ℂ) f) =
        zetaCompletedZeroSideComplex f := by
    rfl
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
        atTop
        (𝓝 z))
    hzeroSideTsum_eq_complex
    hzeroSideTsum

/-- The real parts of the completed-zero residue windows converge to the zero-side Krein
scalar. -/
theorem explicitFormulaCompletedZeroHeightWindowResidueSum_re_tendsto_zeroKreinGram_ownerZeroLimit
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun T : ℝ => Complex.re (explicitFormulaCompletedZeroHeightWindowResidueSum f T))
      atTop
      (𝓝 (zetaCompletedZeroKreinGram f)) := by
  have hcomplex :
      Tendsto
          (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum
  have hre :
      Tendsto
        (fun T : ℝ => Complex.re (explicitFormulaCompletedZeroHeightWindowResidueSum f T))
        atTop
        (𝓝 (Complex.re (zetaCompletedZeroSideComplex f))) :=
    (Complex.continuous_re.tendsto (zetaCompletedZeroSideComplex f)).comp hcomplex
  have htarget :
      Complex.re (zetaCompletedZeroSideComplex f) =
        zetaCompletedZeroKreinGram f := by
    rfl
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun T : ℝ => Complex.re (explicitFormulaCompletedZeroHeightWindowResidueSum f T))
        atTop
        (𝓝 x))
    htarget
    hre

/-- If the contour integrals themselves converge to the completed complex zero side, then
the finite-height residue-window error vanishes. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_of_contourIntegral_tendsto_zeroSideComplex
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f))
    (hcontour :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f))) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyResidueWindowError f F T)
      atTop
      (𝓝 0) := by
  have hwindow :
      Tendsto
          (fun T : ℝ => explicitFormulaCompletedZeroHeightWindowResidueSum f T)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum
  have hsub :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
            explicitFormulaCompletedZeroHeightWindowResidueSum f T)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f - zetaCompletedZeroSideComplex f)) :=
    hcontour.sub hwindow
  have htarget :
      zetaCompletedZeroSideComplex f - zetaCompletedZeroSideComplex f = 0 := by
    exact sub_self _
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyResidueWindowError f F T) =
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
            explicitFormulaCompletedZeroHeightWindowResidueSum f T) := by
    funext T
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) -
              explicitFormulaCompletedZeroHeightWindowResidueSum f T)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- At a scheduled height, the contour integral is the finite residue-window sum plus the
named finite-rectangle residue equality error.

This is only the bookkeeping identity for the named error term; the analytic boundary
avoidance hypothesis belongs to the finite residue theorem below. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_residueSum_add_error
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      explicitFormulaScheduledRectangleResidueSum f F h u +
        explicitFormulaScheduledRectangleResidueEqualityError f F h u := by
  let T : ℝ := h.height_schedule.height u
  have hbase :
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T +
          explicitFormulaFamilyResidueWindowError f F T :=
    zetaCompletedExplicitFormulaContourIntegral_eq_heightWindowResidueSum_add_error f F T
  have hpointwise :
      explicitFormulaScheduledRectangleResidueSum f F h u =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
    unfold explicitFormulaScheduledRectangleResidueSum
    rfl
  have herror :
      explicitFormulaScheduledRectangleResidueEqualityError f F h u =
        explicitFormulaFamilyResidueWindowError f F T := by
    unfold explicitFormulaScheduledRectangleResidueEqualityError
    unfold explicitFormulaScheduledRectangleResidueSum
    unfold explicitFormulaFamilyResidueWindowError
    rfl
  exact Eq.trans hbase
    (congrArg₂ (fun a b : ℂ => a + b) hpointwise.symm herror.symm)

/-- The package schedule gives boundary avoidance at the chosen scheduled rectangle. -/
theorem explicitFormulaScheduledRectangle_avoidsSingularBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaContourFamilyAvoidsSingularBoundary F
      (h.height_schedule.height u) :=
  h.height_schedule.avoids_boundary u

/-- At a scheduled height, every boundary point is off the completed contour-integrand
singular set. -/
theorem completedZetaContourIntegrand_not_mem_singularSet_of_scheduledBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) {z : ℂ}
    (hboundary :
      z ∈ explicitFormulaContourFamilyBoundary F
        (h.height_schedule.height u)) :
    z ∉ completedZetaContourIntegrandSingularSet := by
  exact
    completedZetaContourIntegrand_not_mem_singularSet_of_avoidsBoundary
      F (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hboundary

/-- The completed contour integrand is regular at every boundary point of the chosen
scheduled rectangle. -/
theorem completedZetaContourIntegrand_regularAt_scheduledBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) {z : ℂ}
    (hboundary :
      z ∈ explicitFormulaContourFamilyBoundary F
        (h.height_schedule.height u)) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact
    completedZetaContourIntegrand_regularAt_boundary_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hboundary

/-- Finite rectangle residue theorem with the zero/pole boundary excluded.

At a height whose rectangle boundary avoids the completed-zeta singular set, the contour
integral of the completed explicit-formula integrand is the residue window over the
completed zeros inside that height window. -/
theorem explicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
  exact
    zetaCompletedExplicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_of_finiteRectangleResidueTheorem
      f F h T havoid hfinite

/-- Finite rectangle residue equality at the scheduled height, with boundary avoidance
supplied by the package schedule. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_heightWindowResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    zetaCompletedExplicitFormulaContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f
        (h.height_schedule.height u) := by
  exact
    explicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hfinite

/-- Completed-zeta naming wrapper for the finite avoided-rectangle residue theorem. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_completedZeroHeightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
  exact
    explicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
      f F h T havoid

/-- If the chosen scheduled rectangle has the finite contour/residue equality, then the
named scheduled residue-equality error is zero at that height. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0 := by
  unfold explicitFormulaScheduledRectangleResidueEqualityError
  unfold explicitFormulaScheduledRectangleResidueSum
  change
    zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) -
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u) =
      0
  exact sub_eq_zero.mpr hfinite

/-- Finite scheduled rectangle residue equality at one avoided height.

This is the true finite-rectangle residue-theorem input: boundary avoidance guarantees that
the residue-window computation has no zero/pole hit on the contour, so the named equality
error vanishes at that scheduled height. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (havoid :
      explicitFormulaContourFamilyAvoidsSingularBoundary F
        (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0 := by
  have hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u) :=
    explicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
      f F h (h.height_schedule.height u) havoid
  exact
    explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
      f F h u hfinite

/-- The scheduled rectangle residue-equality error vanishes using the package schedule's
boundary-avoidance certificate. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0 := by
  exact
    explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
      f F h u
      (explicitFormulaScheduledRectangleContourIntegral_eq_heightWindowResidueSum
        f F h u)

/-- Core finite-rectangle contour residue theorem, after zero-excision/window accounting.

This is the scheduled finite-rectangle computation with the boundary-avoidance certificate
kept visible.  The certificate is the progress condition that makes each finite contour
computation admissible along the scheduled realization. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (havoid :
      ∀ u : ℝ,
        explicitFormulaContourFamilyAvoidsSingularBoundary F
          (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError f F h u)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError f F h u) =
        (fun _u : ℝ => (0 : ℂ)) := by
    funext u
    exact explicitFormulaScheduledRectangleResidueEqualityError_eq_zero f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    tendsto_const_nhds

/-- Core finite-rectangle contour residue theorem, after zero-excision/window accounting.

This is the finite-rectangle residue theorem in its zero-side window form: the full
rectangle contour integral differs from the finite zero-side window by an error tending to
zero. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_core_ownerFiniteRectangleResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError f F h u)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality
      f F h
      (fun u => explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)

/-! ## Projected contour spine for vertical channels -/

/-- The scheduled rectangle residue-equality error, viewed as a contour-side input to a
selected vertical channel projection. -/
noncomputable def explicitFormulaScheduledProjectedRectangleResidueEqualityError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (_channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledRectangleResidueEqualityError f F h u

/-- The scheduled horizontal contour error, viewed as an input to a selected vertical channel
projection. -/
noncomputable def explicitFormulaScheduledProjectedHorizontalError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (_channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaFamilyHorizontalResidueWindowError f F
    (h.height_schedule.height u)

/-- The full projected contour spine error combines finite rectangle residue equality,
projected horizontal decay, and projected vertical decomposition. -/
noncomputable def explicitFormulaScheduledProjectedContourSpineError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel +
    explicitFormulaScheduledProjectedHorizontalError f F h u channel +
      explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel

/-- Projecting the finite scheduled rectangle residue equality introduces no new algebra. -/
theorem explicitFormulaScheduledProjectedRectangleResidueEqualityError_eq_rectangleError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel =
      explicitFormulaScheduledRectangleResidueEqualityError f F h u := by
  rfl

/-- The projected finite rectangle residue-equality error vanishes along the scheduled
boundary-avoiding rectangles. -/
theorem explicitFormulaScheduledProjectedRectangleResidueEqualityError_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u) := by
    funext u
    exact
      explicitFormulaScheduledProjectedRectangleResidueEqualityError_eq_rectangleError
        f F h u channel
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_core_ownerFiniteRectangleResidueEquality
      f F h)

/-- Projected horizontal decay for a selected vertical channel. -/
theorem explicitFormulaScheduledProjectedHorizontalError_tendsto_zero_ownerProjectedHorizontalDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedHorizontalError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  exact
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled
      f F.toContourFamily h 1

/-- The projected contour spine error vanishes once the three owner inputs are supplied:
scheduled rectangle residue equality, projected horizontal decay, and projected vertical
decomposition. -/
theorem explicitFormulaScheduledProjectedContourSpineError_tendsto_zero_ownerProjectedContourSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedContourSpineError
          f F.toContourFamily h u channel)
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedRectangleResidueEqualityError_tendsto_zero
      f F.toContourFamily h channel
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedHorizontalError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedHorizontalError_tendsto_zero_ownerProjectedHorizontalDecay
      f F hSchedule channel
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_ownerProjectedVerticalDecomposition
      f F hSchedule channel
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
              f F.toContourFamily h u channel +
            explicitFormulaScheduledProjectedHorizontalError
              f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedVerticalDecompositionError
                f F.toContourFamily h u channel)
        atTop
        (𝓝 (0 + 0 + 0 : ℂ)) :=
    (hresidue.add hhorizontal).add hvertical
  have htarget : (0 + 0 + 0 : ℂ) = 0 := by
    exact Eq.trans (add_zero (0 + 0)) (add_zero 0)
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedContourSpineError
          f F.toContourFamily h u channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedRectangleResidueEqualityError
              f F.toContourFamily h u channel +
            explicitFormulaScheduledProjectedHorizontalError
              f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedVerticalDecompositionError
                f F.toContourFamily h u channel) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaScheduledProjectedRectangleResidueEqualityError
                f F.toContourFamily h u channel +
              explicitFormulaScheduledProjectedHorizontalError
                f F.toContourFamily h u channel +
                explicitFormulaScheduledProjectedVerticalDecompositionError
                  f F.toContourFamily h u channel)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The shared selected-channel transport theorem is a thin wrapper over the projected
vertical-decomposition owner input. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_ownerProjectedContourSpine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F.toContourFamily (h.height_schedule.height u) channel)
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_ownerProjectedVerticalDecomposition
      f F hSchedule channel
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F.toContourFamily (h.height_schedule.height u) channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F.toContourFamily h u channel) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hvertical

/-- Core finite-rectangle contour residue theorem, after zero-excision/window accounting.

The scheduled finite-rectangle residue equality controls the contour-minus-residue error,
and the finite zero-window accounting error is identically zero. -/
theorem explicitFormulaFamilyContourZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyContourZeroSideWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_core_ownerFiniteRectangleResidueEquality
      f F h
  have hwindow :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledZeroWindowAccountingError f F h u)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledZeroWindowAccountingError_tendsto_zero f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u +
            explicitFormulaScheduledZeroWindowAccountingError f F h u)
        atTop
        (𝓝 (0 + 0 : ℂ)) :=
    hresidue.add hwindow
  have htarget : (0 + 0 : ℂ) = 0 :=
    add_zero 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyContourZeroSideWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError f F h u +
            explicitFormulaScheduledZeroWindowAccountingError f F h u) := by
    funext u
    exact
      explicitFormulaFamilyContourZeroSideWindowError_scheduled_eq_residueEquality_add_accounting
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaScheduledRectangleResidueEqualityError f F h u +
              explicitFormulaScheduledZeroWindowAccountingError f F h u)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Core finite-rectangle vertical zero-side theorem.

This is the finite-rectangle residue-calculus input after zero-excision/window
normalization and after removing the horizontal contour sides: the right-minus-left
vertical side differs from the finite zero-side window by an error tending to zero. -/
theorem explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hcontour :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyContourZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled f F h 1
  have hsub :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 - 0 : ℂ)) :=
    hcontour.sub hhorizontal
  have htarget : (0 - 0 : ℂ) = 0 :=
    sub_self 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalZeroSideWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyContourZeroSideWindowError f F
              (h.height_schedule.height u) -
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaFamilyVerticalZeroSideWindowError_eq_contourZeroSide_sub_horizontal
      f F (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyContourZeroSideWindowError f F
                (h.height_schedule.height u) -
              explicitFormulaFamilyHorizontalResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- The vertical residue-window error vanishes by zero-excision/window equality from the
zero-side finite-rectangle residue theorem. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hzeroSide :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalZeroSideWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyVerticalZeroSideWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalZeroSideWindowError f F
            (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaFamilyVerticalResidueWindowError_eq_zeroSideWindowError
      f F (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hzeroSide

/-- Core finite-rectangle residue-calculus error theorem.

The full contour residue-window error splits into the vertical finite-residue error plus
the horizontal side error.  The finite-rectangle residue theorem controls the former, and
horizontal edge decay controls the latter. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_core_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_core_ownerFiniteRectangleResidueTheorem
      f F h
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled f F h 1
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 + 0 : ℂ)) :=
    hvertical.add hhorizontal
  have htarget : (0 + 0 : ℂ) = 0 :=
    add_zero 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaFamilyResidueWindowError_eq_vertical_add_horizontal
      f F (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyVerticalResidueWindowError f F
                (h.height_schedule.height u) +
              explicitFormulaFamilyHorizontalResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Core contour-residue assembly theorem.

This contour-side residue theorem is assembled from finite-rectangle residue calculus,
with the pointwise scheduled primitive
`explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality`
providing the boundary-avoiding rectangle computation. -/
theorem zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_core_ownerContourResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  have hwindow :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)) :=
    (explicitFormulaCompletedZeroHeightWindowResidueSum_tendsto_zeroSideComplex_ownerZeroLimit f hsum).comp
      h.height_schedule.cofinal
  have herror :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyResidueWindowError_tendsto_zero_core_ownerResidueCalculus f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaCompletedZeroHeightWindowResidueSum f
              (h.height_schedule.height u) +
            explicitFormulaFamilyResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f + 0)) :=
    hwindow.add herror
  have htarget :
      zetaCompletedZeroSideComplex f + 0 =
        zetaCompletedZeroSideComplex f :=
    add_zero _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          explicitFormulaCompletedZeroHeightWindowResidueSum f
              (h.height_schedule.height u) +
            explicitFormulaFamilyResidueWindowError f F
              (h.height_schedule.height u)) := by
    funext u
    exact zetaCompletedExplicitFormulaContourIntegral_eq_heightWindowResidueSum_add_error
      f F (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop (𝓝 (zetaCompletedZeroSideComplex f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaCompletedZeroHeightWindowResidueSum f
                (h.height_schedule.height u) +
              explicitFormulaFamilyResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Owner finite-rectangle residue-calculus error theorem.

After the finite completed-zero height-window residue sum is subtracted from the
rectangle contour integral, the residual rectangle error tends to zero along an admissible
contour family. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaFamilyResidueWindowError_tendsto_zero_core_ownerResidueCalculus
      f F.toContourFamily
      (explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule)

/-- The completed-zeta rectangle residue calculus reconstructs the complex zero-side
residue sum from the limiting contour integral. -/
theorem zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ) f)) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaContourIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) := by
  exact
    zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_core_ownerContourResidueTheorem
      f F.toContourFamily
      (explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule)
      hsum

/-- The vertical-boundary remainder along the contour family, still complex-valued. -/
noncomputable def zetaCompletedExplicitFormulaVerticalBoundaryRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The vertical side difference is the analytic boundary sum plus its complex remainder. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_eq_boundarySum_add_boundaryRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f +
        zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T := by
  let V : ℂ :=
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  let B : ℂ := zetaCompletedExplicitFormulaBoundarySumAnalytic f
  unfold zetaCompletedExplicitFormulaVerticalBoundaryRemainder
  change V = B + (V - B)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-B + B) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel B).symm
    _ = (V + -B) + B := by
      exact (add_assoc V (-B) B).symm
    _ = B + (V + -B) := by
      exact add_comm (V + -B) B
    _ = B + (V - B) := by
      exact congrArg (fun x : ℂ => B + x) (sub_eq_add_neg V B).symm

/-- If the complex vertical-boundary remainder vanishes, then the vertical side difference
converges to the analytic boundary sum. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_of_boundaryRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hremainder :
      Tendsto
        (fun T : ℝ => zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaBoundarySumAnalytic f +
            zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0)) :=
    hconst.add hremainder
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0 =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    add_zero _
  have hpointwise :
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) =
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaBoundarySumAnalytic f +
            zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T) := by
    funext T
    exact
      zetaCompletedExplicitFormulaVerticalDifference_eq_boundarySum_add_boundaryRemainder
        f F T
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            zetaCompletedExplicitFormulaBoundarySumAnalytic f +
              zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- If the vertical side difference converges to the analytic boundary sum, then the named
vertical-boundary remainder vanishes. -/
theorem zetaCompletedExplicitFormulaVerticalBoundaryRemainder_tendsto_zero_of_verticalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hvertical :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) :
    Tendsto
      (fun T : ℝ => zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T)
      atTop
      (𝓝 0) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun T : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic f -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hvertical.sub hconst
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f -
          zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        0 := by
    exact sub_self _
  have hpointwise :
      (fun T : ℝ => zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F T) =
        (fun T : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
    funext T
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
                zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) -
              zetaCompletedExplicitFormulaBoundarySumAnalytic f)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-! ## Vertical-channel public wrappers -/

/-- Public wrapper for prime vertical-channel convergence. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerPrimeVerticalChannel
      f F hSchedule

/-- Public wrapper for archimedean vertical-channel convergence. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanVerticalChannel
      f F hSchedule

/-- Public wrapper for correction vertical-channel convergence. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerCorrectionVerticalChannel
      f F hSchedule

/-- The three named vertical channels converge to the analytic boundary sum. -/
theorem zetaCompletedExplicitFormulaVerticalChannelSum_tendsto_boundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hprime :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution f F hSchedule
  have harch :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution
      f F hSchedule
  have hcorr :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) :=
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution
      f F hSchedule
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
              (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
              (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
                (h.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaPrimeContribution f +
            zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionContribution f)) :=
    (hprime.add harch).add hcorr
  have htarget :
      zetaCompletedExplicitFormulaPrimeContribution f +
          zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionContribution f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
    rfl
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
              (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
              (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
                (h.height_schedule.height u)) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
                (h.height_schedule.height T) +
              zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
                (h.height_schedule.height T) +
                zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
                  (h.height_schedule.height T))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-! ## Completed vertical packet realization owner -/

/-- Pointwise packet decomposition after the completed log-derivative normalization:
the completed boundary object splits into prime, archimedean, and correction channels. -/
theorem zetaCompletedExplicitFormulaVerticalIntegrand_eq_channelIntegrands_ownerCompletedLogDerivativeDecomposition
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    completedZetaNegLogDeriv s * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) =
      explicitFormulaPrimeLogDerivative s * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative s *
          zetaCompletedExplicitFormulaPhi f (s - 1 / 2) +
        explicitFormulaCorrectionLogDerivative s *
          zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  let Φ : ℂ := zetaCompletedExplicitFormulaPhi f (s - 1 / 2)
  let P : ℂ := explicitFormulaPrimeLogDerivative s
  let A : ℂ := explicitFormulaArchimedeanLogDerivative s
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  have hlog :
      completedZetaNegLogDeriv s = P + A + C := by
    exact completedZetaNegLogDeriv_eq_explicitFormulaCompletedLogDerivative_ownerCompletedLogDerivativeDecomposition
      s
  change completedZetaNegLogDeriv s * Φ = P * Φ + A * Φ + C * Φ
  calc
    completedZetaNegLogDeriv s * Φ = (P + A + C) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hlog
    _ = (P + A) * Φ + C * Φ := by
      exact add_mul (P + A) C Φ
    _ = (P * Φ + A * Φ) + C * Φ := by
      exact congrArg (fun z : ℂ => z + C * Φ) (add_mul P A Φ)
    _ = P * Φ + A * Φ + C * Φ := by
      rfl

/-- The completed vertical realization remainder after subtracting the realized channel
packet from the completed vertical boundary object. -/
noncomputable def zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)) -
    zetaCompletedExplicitFormulaVerticalChannelSum f F T

/-- Subtracting two three-term sums is the sum of the three component differences. -/
theorem complex_three_add_sub_three_add_eq
    (a b c d e g : ℂ) :
    (a + b + c) - (d + e + g) =
      (a - d) + (b - e) + (c - g) := by
  calc
    (a + b + c) - (d + e + g) =
        (a + (b + c)) - (d + (e + g)) := by
      exact congrArg₂ Sub.sub
        (add_assoc a b c)
        (add_assoc d e g)
    _ = (a - d) + ((b + c) - (e + g)) := by
      exact add_sub_add_comm a (b + c) d (e + g)
    _ = (a - d) + ((b - e) + (c - g)) := by
      exact congrArg (fun z : ℂ => (a - d) + z)
        (add_sub_add_comm b c e g)
    _ = (a - d) + (b - e) + (c - g) := by
      exact (add_assoc (a - d) (b - e) (c - g)).symm

/-- Set-integral additivity for a three-term complex-valued sum. -/
theorem complex_setIntegral_three_add_eq_sum_integrals
    (S : Set ℝ) (P A C : ℝ → ℂ)
    (hP : IntegrableOn P S)
    (hA : IntegrableOn A S)
    (hC : IntegrableOn C S) :
    (∫ t in S, P t + A t + C t) =
      (∫ t in S, P t) + (∫ t in S, A t) + (∫ t in S, C t) := by
  have hPA : IntegrableOn (fun t : ℝ => P t + A t) S :=
    hP.add hA
  calc
    (∫ t in S, P t + A t + C t) =
        (∫ t in S, P t + A t) + ∫ t in S, C t := by
      exact integral_add hPA hC
    _ = ((∫ t in S, P t) + ∫ t in S, A t) + ∫ t in S, C t := by
      exact congrArg (fun z : ℂ => z + ∫ t in S, C t) (integral_add hP hA)
    _ = (∫ t in S, P t) + (∫ t in S, A t) + (∫ t in S, C t) := by
      rfl

/-- Continuous complex-valued functions on a compact real interval are integrable on that
interval.  This is the generic compact-regularity bridge used by the vertical channel
packet; analytic channel regularity is kept in the packet-continuity owner theorem below. -/
theorem complex_continuousOn_Icc_integrableOn
    {a b : ℝ} {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.Icc a b)) :
    IntegrableOn g (Set.Icc a b) := by
  exact hg.integrableOn_compact isCompact_Icc

/-- Right vertical realization of the pointwise completed channel-packet decomposition before
distributing the interval integral over the three channel summands. -/
theorem zetaCompletedExplicitFormulaRightLineIntegral_eq_integral_channelSum_ownerVerticalPointwiseTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
      ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
  unfold zetaCompletedExplicitFormulaRightLineIntegral
  exact integral_congr_ae
    (Filter.Eventually.of_forall
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaVerticalIntegrand_eq_channelIntegrands_ownerCompletedLogDerivativeDecomposition
          f (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t)))

/-- The three completed vertical channel summands in the boundary packet. -/
inductive ExplicitFormulaVerticalChannel where
  | prime
  | archimedean
  | correction

/-- The two vertical sides realizing a completed boundary packet. -/
inductive ExplicitFormulaVerticalSide where
  | right
  | left

/-- The path associated to a vertical side of the rectangle. -/
def explicitFormulaVerticalSidePath
    (side : ExplicitFormulaVerticalSide) (r : ExplicitFormulaRectangle) (t : ℝ) : ℂ :=
  match side with
  | ExplicitFormulaVerticalSide.right => zetaCompletedExplicitFormulaRightPath r t
  | ExplicitFormulaVerticalSide.left => zetaCompletedExplicitFormulaLeftPath r t

/-- The logarithmic derivative associated to a vertical channel of the completed packet. -/
def explicitFormulaVerticalChannelLogDerivative
    (channel : ExplicitFormulaVerticalChannel) (s : ℂ) : ℂ :=
  match channel with
  | ExplicitFormulaVerticalChannel.prime => explicitFormulaPrimeLogDerivative s
  | ExplicitFormulaVerticalChannel.archimedean => explicitFormulaArchimedeanLogDerivative s
  | ExplicitFormulaVerticalChannel.correction => explicitFormulaCorrectionLogDerivative s

/-- A single realized channel integrand on a chosen vertical side. -/
def explicitFormulaVerticalChannelIntegrand
    (f : ZetaAdmissibleFunction) (side : ExplicitFormulaVerticalSide)
    (channel : ExplicitFormulaVerticalChannel) (r : ExplicitFormulaRectangle) (t : ℝ) : ℂ :=
  explicitFormulaVerticalChannelLogDerivative channel
      (explicitFormulaVerticalSidePath side r t) *
    zetaCompletedExplicitFormulaPhi f
      (explicitFormulaVerticalSidePath side r t - 1 / 2)

/-- The vertical side parametrizations are affine, hence continuous. -/
theorem explicitFormulaVerticalSidePath_continuous
    (side : ExplicitFormulaVerticalSide) (r : ExplicitFormulaRectangle) :
    Continuous (fun t : ℝ => explicitFormulaVerticalSidePath side r t) := by
  cases side
  · unfold explicitFormulaVerticalSidePath
    unfold zetaCompletedExplicitFormulaRightPath
    exact continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  · unfold explicitFormulaVerticalSidePath
    unfold zetaCompletedExplicitFormulaLeftPath
    exact continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- The shifted completed explicit-formula transform is continuous. -/
theorem zetaCompletedExplicitFormulaPhi_shift_continuous
    (f : ZetaAdmissibleFunction) :
    Continuous
      (fun s : ℂ => zetaCompletedExplicitFormulaPhi f (s - 1 / 2)) := by
  exact continuous_iff_continuousAt.2
    (fun s =>
      (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
        (zetaPhiAnalyticControl_of_admissible f) s).continuousAt)

/-- A point on a vertical side image is a point on the contour-family boundary. -/
theorem explicitFormulaVerticalSidePath_mem_boundary_of_mem_image
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (side : ExplicitFormulaVerticalSide) {z : ℂ}
    (hz :
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :
    z ∈ explicitFormulaContourFamilyBoundary F T := by
  rcases hz with ⟨t, _ht, rfl⟩
  cases side
  · unfold explicitFormulaVerticalSidePath
    unfold explicitFormulaContourFamilyBoundary
    exact Or.inl ⟨t, rfl⟩
  · unfold explicitFormulaVerticalSidePath
    unfold explicitFormulaContourFamilyBoundary
    exact Or.inr (Or.inl ⟨t, rfl⟩)

/-- The scheduled vertical side image avoids the pole at `0`. -/
theorem explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        z ≠ 0 := by
  intro z hz hz0
  exact havoid z
    (Or.inl hz0)
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- The scheduled vertical side image avoids the pole at `1`. -/
theorem explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        z ≠ 1 := by
  intro z hz hz1
  exact havoid z
    (Or.inr (Or.inl hz1))
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- The scheduled vertical side image avoids Gamma-normalization zeros. -/
theorem explicitFormulaVerticalSidePath_image_Gammaℝ_ne_zero_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        Gammaℝ z ≠ 0 := by
  intro z hz hΓ
  exact havoid z
    (Or.inr (Or.inr (Or.inl hΓ)))
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- The scheduled vertical side image avoids the archimedean half-argument Gamma zeros. -/
theorem explicitFormulaVerticalSidePath_image_Gammaℝ_half_ne_zero_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        Gammaℝ (z / 2) ≠ 0 := by
  intro z hz hΓ
  exact havoid z
    (Or.inr (Or.inr (Or.inr (Or.inl hΓ))))
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- The scheduled vertical side image avoids completed-zeta zeros. -/
theorem explicitFormulaVerticalSidePath_image_completedRiemannZeta_ne_zero_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ∀ z : ℂ,
      z ∈ explicitFormulaVerticalSidePath side (F.rectangle T) ''
          Set.Icc (-(F.rectangle T).T) (F.rectangle T).T →
        completedRiemannZeta z ≠ 0 := by
  intro z hz hΛ
  have hz0 : z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hz1 : z ≠ 1 :=
    explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
      F T havoid side z hz
  exact havoid z
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨hz0, hz1, hΛ⟩))))
    (explicitFormulaVerticalSidePath_mem_boundary_of_mem_image F T side hz)

/-- Prime-channel log-derivative continuity on a scheduled vertical side image. -/
theorem explicitFormulaPrimeLogDerivative_continuousOn_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ContinuousOn
      explicitFormulaPrimeLogDerivative
      (explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  intro z hz
  have hz0 : z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hz1 : z ≠ 1 :=
    explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
      F T havoid side z hz
  have hΛ : completedRiemannZeta z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_completedRiemannZeta_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hΓ : Gammaℝ z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_Gammaℝ_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  exact
    (explicitFormulaPrimeLogDerivative_continuousAt_of_regular z hz0 hz1 hΛ hΓ).continuousWithinAt

/-- Archimedean-channel log-derivative continuity on a scheduled vertical side image. -/
theorem explicitFormulaArchimedeanLogDerivative_continuousOn_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ContinuousOn
      explicitFormulaArchimedeanLogDerivative
      (explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  intro z hz
  have hz0 : z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hz1 : z ≠ 1 :=
    explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
      F T havoid side z hz
  have hΛ : completedRiemannZeta z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_completedRiemannZeta_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  have hΓ : Gammaℝ z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_Gammaℝ_ne_zero_of_avoidsSingularBoundary
      F T havoid side z hz
  exact
    (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
      z hz0 hz1 hΛ hΓ).continuousWithinAt

/-- Correction-channel log-derivative continuity on a scheduled vertical side image. -/
theorem explicitFormulaCorrectionLogDerivative_continuousOn_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) :
    ContinuousOn
      explicitFormulaCorrectionLogDerivative
      (explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  let S : Set ℂ :=
    explicitFormulaVerticalSidePath side (F.rectangle T) ''
      Set.Icc (-(F.rectangle T).T) (F.rectangle T).T
  have hne0 : ∀ z : ℂ, z ∈ S → z ≠ 0 :=
    explicitFormulaVerticalSidePath_image_ne_zero_of_avoidsSingularBoundary
      F T havoid side
  have hne1 : ∀ z : ℂ, z ∈ S → z - 1 ≠ 0 := by
    intro z hz hzsub
    have hz1 : z = 1 := sub_eq_zero.mp hzsub
    exact
      explicitFormulaVerticalSidePath_image_ne_one_of_avoidsSingularBoundary
        F T havoid side z hz hz1
  have hconst_neg_one : ContinuousOn (fun _z : ℂ => (-(1 : ℂ))) S :=
    continuous_const.continuousOn
  have hconst_one : ContinuousOn (fun _z : ℂ => (1 : ℂ)) S :=
    continuous_const.continuousOn
  have hid : ContinuousOn (fun z : ℂ => z) S :=
    continuous_id.continuousOn
  have hsub_one : ContinuousOn (fun z : ℂ => z - 1) S :=
    hid.sub hconst_one
  have hfirst : ContinuousOn (fun z : ℂ => -(1 : ℂ) / z) S :=
    hconst_neg_one.div hid hne0
  have hsecond : ContinuousOn (fun z : ℂ => (1 : ℂ) / (z - 1)) S :=
    hconst_one.div hsub_one hne1
  unfold explicitFormulaCorrectionLogDerivative
  change ContinuousOn (fun z : ℂ => -(1 : ℂ) / z - (1 : ℂ) / (z - 1)) S
  exact hfirst.sub hsecond

/-- Channel log-derivative continuity on the scheduled vertical-edge image, with the
zero/pole boundary exclusions supplied uniformly by the contour-family certificate. -/
theorem explicitFormulaVerticalChannelLogDerivative_continuousOn_of_avoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) (channel : ExplicitFormulaVerticalChannel) :
    ContinuousOn
      (fun s : ℂ => explicitFormulaVerticalChannelLogDerivative channel s)
      (explicitFormulaVerticalSidePath side (F.rectangle T) ''
        Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  cases channel
  · exact explicitFormulaPrimeLogDerivative_continuousOn_of_avoidsBoundary F T havoid side
  · exact explicitFormulaArchimedeanLogDerivative_continuousOn_of_avoidsBoundary F T havoid side
  · exact explicitFormulaCorrectionLogDerivative_continuousOn_of_avoidsBoundary F T havoid side

/-- Compact finite-edge continuity for one realized channel on one vertical side.

This is the single channel-regularity owner theorem.  The correction channel consumes the
same boundary-avoidance certificate as the residue theorem; prime and archimedean channels
are handled by the same statement so they do not become separate roots. -/
theorem explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (side : ExplicitFormulaVerticalSide) (channel : ExplicitFormulaVerticalChannel) :
    ContinuousOn
      (fun t : ℝ =>
        explicitFormulaVerticalChannelIntegrand f side channel (F.rectangle T) t)
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  let S : Set ℝ := Set.Icc (-(F.rectangle T).T) (F.rectangle T).T
  let γ : ℝ → ℂ := fun t => explicitFormulaVerticalSidePath side (F.rectangle T) t
  have hγ : Continuous γ := by
    exact explicitFormulaVerticalSidePath_continuous side (F.rectangle T)
  have hγS : ContinuousOn γ S := hγ.continuousOn
  have hlog_on_image :
      ContinuousOn
        (fun s : ℂ => explicitFormulaVerticalChannelLogDerivative channel s)
        (γ '' S) := by
    exact
      explicitFormulaVerticalChannelLogDerivative_continuousOn_of_avoidsSingularBoundary
        F T havoid side channel
  have hlog :
      ContinuousOn
        (fun t : ℝ => explicitFormulaVerticalChannelLogDerivative channel (γ t))
        S := by
    exact hlog_on_image.comp hγS (fun t ht => ⟨t, ht, rfl⟩)
  have hphi_cont :
      Continuous
        (fun s : ℂ => zetaCompletedExplicitFormulaPhi f (s - 1 / 2)) :=
    zetaCompletedExplicitFormulaPhi_shift_continuous f
  have hphi :
      ContinuousOn
        (fun t : ℝ => zetaCompletedExplicitFormulaPhi f (γ t - 1 / 2))
        S := by
    exact (hphi_cont.comp hγ).continuousOn
  change
    ContinuousOn
      (fun t : ℝ =>
        explicitFormulaVerticalChannelLogDerivative channel (γ t) *
          zetaCompletedExplicitFormulaPhi f (γ t - 1 / 2))
      S
  exact hlog.mul hphi

/-- Compact finite-edge continuity of the realized vertical channel packet away from
singular boundary hits.

This is the single analytic regularity owner for the finite vertical edges.  The correction
channel uses `havoid`; the prime and archimedean channels are included in the same packet so
right/left and channel projections do not become independent roots. -/
theorem zetaCompletedExplicitFormulaVerticalChannelPacket_continuousOn_ownerCompactRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (ContinuousOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) ∧
    (ContinuousOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) := by
  have hRP :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.right
            ExplicitFormulaVerticalChannel.prime
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      f F T havoid ExplicitFormulaVerticalSide.right ExplicitFormulaVerticalChannel.prime
  have hRA :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.right
            ExplicitFormulaVerticalChannel.archimedean
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      f F T havoid ExplicitFormulaVerticalSide.right ExplicitFormulaVerticalChannel.archimedean
  have hRC :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.right
            ExplicitFormulaVerticalChannel.correction
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      f F T havoid ExplicitFormulaVerticalSide.right ExplicitFormulaVerticalChannel.correction
  have hLP :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.left
            ExplicitFormulaVerticalChannel.prime
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      f F T havoid ExplicitFormulaVerticalSide.left ExplicitFormulaVerticalChannel.prime
  have hLA :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.left
            ExplicitFormulaVerticalChannel.archimedean
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      f F T havoid ExplicitFormulaVerticalSide.left ExplicitFormulaVerticalChannel.archimedean
  have hLC :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaVerticalChannelIntegrand f
            ExplicitFormulaVerticalSide.left
            ExplicitFormulaVerticalChannel.correction
            (F.rectangle T) t)
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    explicitFormulaVerticalChannelIntegrand_continuousOn_ownerCompactRegularity
      f F T havoid ExplicitFormulaVerticalSide.left ExplicitFormulaVerticalChannel.correction
  exact ⟨⟨hRP, hRA, hRC⟩, ⟨hLP, hLA, hLC⟩⟩

/-- Compact finite-edge regularity of the realized vertical channel packet away from
singular boundary hits.

This is the single owner regularity input for vertical channel realization.  The right and
left packet integrability lemmas, and their prime/archimedean/correction projections, are
thin consumers of this theorem. -/
theorem zetaCompletedExplicitFormulaVerticalChannelPacket_integrable_ownerCompactRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) ∧
    (IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) := by
  have hcont :
      (ContinuousOn
          (fun t : ℝ =>
            explicitFormulaPrimeLogDerivative
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
        ContinuousOn
          (fun t : ℝ =>
            explicitFormulaArchimedeanLogDerivative
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
        ContinuousOn
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) ∧
      (ContinuousOn
          (fun t : ℝ =>
            explicitFormulaPrimeLogDerivative
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
        ContinuousOn
          (fun t : ℝ =>
            explicitFormulaArchimedeanLogDerivative
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
        ContinuousOn
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
          (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)) :=
    zetaCompletedExplicitFormulaVerticalChannelPacket_continuousOn_ownerCompactRegularity
      f F T havoid
  exact
    ⟨⟨complex_continuousOn_Icc_integrableOn hcont.1.1,
        complex_continuousOn_Icc_integrableOn hcont.1.2.1,
        complex_continuousOn_Icc_integrableOn hcont.1.2.2⟩,
      ⟨complex_continuousOn_Icc_integrableOn hcont.2.1,
        complex_continuousOn_Icc_integrableOn hcont.2.2.1,
        complex_continuousOn_Icc_integrableOn hcont.2.2.2⟩⟩

/-- Scheduled compact finite-edge regularity of the realized vertical channel packet. -/
theorem zetaCompletedExplicitFormulaScheduledVerticalChannelPacket_integrable_ownerCompactRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T)) ∧
    (IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        (Set.Icc (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T)) :=
  zetaCompletedExplicitFormulaVerticalChannelPacket_integrable_ownerCompactRegularity
    f F (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)

/-- Finite-edge regularity of the realized right vertical channel packet away from scheduled
singular boundary hits. -/
theorem zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaVerticalChannelPacket_integrable_ownerCompactRegularity
      f F T havoid).1

/-- Finite-edge integrability of the realized right prime channel. -/
theorem zetaCompletedExplicitFormulaRightPrimeChannelIntegrand_integrable_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
      f F T havoid).1

/-- Finite-edge integrability of the realized right archimedean channel. -/
theorem zetaCompletedExplicitFormulaRightArchimedeanChannelIntegrand_integrable_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
      f F T havoid).2.1

/-- Finite-edge integrability of the realized right correction channel. -/
theorem zetaCompletedExplicitFormulaRightCorrectionChannelIntegrand_integrable_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
      f F T havoid).2.2

/-- Finite-edge integrability of the realized right vertical channel packet. -/
theorem zetaCompletedExplicitFormulaRightChannelIntegrands_integrable_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact zetaCompletedExplicitFormulaRightChannelPacket_integrable_ownerVerticalRegularity
    f F T havoid

/-- Right vertical realization preserves the finite direct sum of channel summands. -/
theorem zetaCompletedExplicitFormulaRightChannelIntegralSum_eq_sum_channelIntegrals_ownerIntervalIntegralAdditivity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
  exact
    complex_setIntegral_three_add_eq_sum_integrals
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (zetaCompletedExplicitFormulaRightChannelIntegrands_integrable_ownerVerticalIntegralTransport
        f F T havoid).1
      (zetaCompletedExplicitFormulaRightChannelIntegrands_integrable_ownerVerticalIntegralTransport
        f F T havoid).2.1
      (zetaCompletedExplicitFormulaRightChannelIntegrands_integrable_ownerVerticalIntegralTransport
        f F T havoid).2.2

/-- Right vertical realization transport from the completed boundary object to the channel
packet. -/
theorem zetaCompletedExplicitFormulaRightLineIntegral_eq_channelIntegrals_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
  exact
    (zetaCompletedExplicitFormulaRightLineIntegral_eq_integral_channelSum_ownerVerticalPointwiseTransport
      f F T).trans
      (zetaCompletedExplicitFormulaRightChannelIntegralSum_eq_sum_channelIntegrals_ownerIntervalIntegralAdditivity
        f F T havoid)

/-- Left vertical realization of the pointwise completed channel-packet decomposition before
distributing the interval integral over the three channel summands. -/
theorem zetaCompletedExplicitFormulaLeftLineIntegral_eq_integral_channelSum_ownerVerticalPointwiseTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
  unfold zetaCompletedExplicitFormulaLeftLineIntegral
  exact integral_congr_ae
    (Filter.Eventually.of_forall
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaVerticalIntegrand_eq_channelIntegrands_ownerCompletedLogDerivativeDecomposition
          f (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)))

/-- Finite-edge regularity of the realized left vertical channel packet away from scheduled
singular boundary hits. -/
theorem zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaVerticalChannelPacket_integrable_ownerCompactRegularity
      f F T havoid).2

/-- Finite-edge integrability of the realized left prime channel. -/
theorem zetaCompletedExplicitFormulaLeftPrimeChannelIntegrand_integrable_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
      f F T havoid).1

/-- Finite-edge integrability of the realized left archimedean channel. -/
theorem zetaCompletedExplicitFormulaLeftArchimedeanChannelIntegrand_integrable_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
      f F T havoid).2.1

/-- Finite-edge integrability of the realized left correction channel. -/
theorem zetaCompletedExplicitFormulaLeftCorrectionChannelIntegrand_integrable_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact
    (zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
      f F T havoid).2.2

/-- Finite-edge integrability of the realized left vertical channel packet. -/
theorem zetaCompletedExplicitFormulaLeftChannelIntegrands_integrable_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) ∧
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  exact zetaCompletedExplicitFormulaLeftChannelPacket_integrable_ownerVerticalRegularity
    f F T havoid

/-- Left vertical realization preserves the finite direct sum of channel summands. -/
theorem zetaCompletedExplicitFormulaLeftChannelIntegralSum_eq_sum_channelIntegrals_ownerIntervalIntegralAdditivity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
  exact
    complex_setIntegral_three_add_eq_sum_integrals
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T)
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (zetaCompletedExplicitFormulaLeftChannelIntegrands_integrable_ownerVerticalIntegralTransport
        f F T havoid).1
      (zetaCompletedExplicitFormulaLeftChannelIntegrands_integrable_ownerVerticalIntegralTransport
        f F T havoid).2.1
      (zetaCompletedExplicitFormulaLeftChannelIntegrands_integrable_ownerVerticalIntegralTransport
        f F T havoid).2.2

/-- Left vertical realization transport from the completed boundary object to the channel
packet. -/
theorem zetaCompletedExplicitFormulaLeftLineIntegral_eq_channelIntegrals_ownerVerticalIntegralTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
  exact
    (zetaCompletedExplicitFormulaLeftLineIntegral_eq_integral_channelSum_ownerVerticalPointwiseTransport
      f F T).trans
      (zetaCompletedExplicitFormulaLeftChannelIntegralSum_eq_sum_channelIntegrals_ownerIntervalIntegralAdditivity
        f F T havoid)

/-- The right-minus-left vertical realization of the completed object is the realized channel
packet. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_eq_channelSum_of_right_left_transport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hright :
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)))
    (hleft :
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) +
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      zetaCompletedExplicitFormulaVerticalChannelSum f F T := by
  let RP : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let RA : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let RC : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let LP : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  let LA : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  let LC : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  have hright' :
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
        RP + RA + RC := hright
  have hleft' :
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        LP + LA + LC := hleft
  calc
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        (RP + RA + RC) - (LP + LA + LC) := by
      exact congrArg₂ Sub.sub hright' hleft'
    _ = (RP - LP) + (RA - LA) + (RC - LC) := by
      exact complex_three_add_sub_three_add_eq RP RA RC LP LA LC
    _ = zetaCompletedExplicitFormulaVerticalChannelSum f F T := by
      unfold zetaCompletedExplicitFormulaVerticalChannelSum
      unfold zetaCompletedExplicitFormulaPrimeVerticalChannel
      unfold zetaCompletedExplicitFormulaArchimedeanVerticalChannel
      unfold zetaCompletedExplicitFormulaCorrectionVerticalChannel
      rfl

/-- The completed log-derivative decomposition transported through the right and left
vertical integrals gives the channel-sum identity at a fixed height. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_eq_channelSum_ownerCompletedLogDerivativeDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
      zetaCompletedExplicitFormulaVerticalChannelSum f F T := by
  exact
    zetaCompletedExplicitFormulaVerticalDifference_eq_channelSum_of_right_left_transport
      f F T
      (zetaCompletedExplicitFormulaRightLineIntegral_eq_channelIntegrals_ownerVerticalIntegralTransport
        f F T havoid)
      (zetaCompletedExplicitFormulaLeftLineIntegral_eq_channelIntegrals_ownerVerticalIntegralTransport
        f F T havoid)

/-- The vertical-channel comparison remainder is pointwise zero. -/
theorem zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder f F T = 0 := by
  unfold zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder
  exact sub_eq_zero.mpr
    (zetaCompletedExplicitFormulaVerticalDifference_eq_channelSum_ownerCompletedLogDerivativeDecomposition
      f F T havoid)

/-- The scheduled completed vertical-channel comparison remainder is pointwise zero. -/
theorem zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_scheduled_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder f F
        (h.height_schedule.height u) = 0 :=
  zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_eq_zero
    f F (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)

/-- The scheduled completed vertical-channel comparison remainder tends to zero. -/
theorem zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder f F
          (h.height_schedule.height u)) =
        (fun _T : ℝ => (0 : ℂ)) := by
    funext u
    exact zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_scheduled_eq_zero f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    tendsto_const_nhds

/-- The actual completed log-derivative vertical side is asymptotic to the sum of the
prime, archimedean, and correction channels. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_sub_channelSum_tendsto_zero_ownerCompletedVerticalChannelComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.rectangle (h.height_schedule.height u))) -
          zetaCompletedExplicitFormulaVerticalChannelSum f F
            (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact zetaCompletedExplicitFormulaVerticalChannelComparisonRemainder_tendsto_zero f F h

/-- Public wrapper for the completed vertical side/channel-sum comparison. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_sub_channelSum_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.rectangle (h.height_schedule.height u))) -
          zetaCompletedExplicitFormulaVerticalChannelSum f F
            (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaVerticalDifference_sub_channelSum_tendsto_zero_ownerCompletedVerticalChannelComparison
      f F h

/-- Core vertical-decomposition owner theorem.

This is the vertical contour theorem to prove by decomposing the completed negative
log-derivative into its prime, archimedean, and correction terms: the right-minus-left
vertical contour contribution converges to the analytic boundary sum. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hcomparison :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u)) -
              zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u))) -
            zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
              (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaVerticalDifference_sub_channelSum_tendsto_zero
      f F.toContourFamily h
  have hchannels :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    zetaCompletedExplicitFormulaVerticalChannelSum_tendsto_boundarySum f F hSchedule
  have hsum :
      Tendsto
        (fun u : ℝ =>
          ((zetaCompletedExplicitFormulaRightLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u)) -
                zetaCompletedExplicitFormulaLeftLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u))) -
              zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
                (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 + zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hcomparison.add hchannels
  have htarget :
      0 + zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    zero_add _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u))) =
        (fun u : ℝ =>
          ((zetaCompletedExplicitFormulaRightLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u)) -
                zetaCompletedExplicitFormulaLeftLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u))) -
              zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
                (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
              (h.height_schedule.height u)) := by
    funext u
    exact (sub_add_cancel
      (zetaCompletedExplicitFormulaRightLineIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)) -
        zetaCompletedExplicitFormulaLeftLineIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)))
      (zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
        (h.height_schedule.height u))).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            ((zetaCompletedExplicitFormulaRightLineIntegral f
                    (F.toContourFamily.rectangle (h.height_schedule.height T)) -
                  zetaCompletedExplicitFormulaLeftLineIntegral f
                    (F.toContourFamily.rectangle (h.height_schedule.height T))) -
                zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
                  (h.height_schedule.height T)) +
              zetaCompletedExplicitFormulaVerticalChannelSum f F.toContourFamily
                (h.height_schedule.height T))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Two scheduled vertically regular contour realizations reconstruct the same completed
boundary scalar.

This is the contour-realization invariance surface used by downstream assembly: the
chosen scheduled vertical measurements are not erased, but each is transported to the same
completed boundary object. -/
theorem zetaCompletedExplicitFormulaScheduledVerticalRealizations_reconstruct_sameBoundaryScalar
    (f : ZetaAdmissibleFunction)
    (F₁ F₂ : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule₁ : ExplicitFormulaCofinalHeightSchedule F₁.toContourFamily)
    (hSchedule₂ : ExplicitFormulaCofinalHeightSchedule F₂.toContourFamily) :
    (Tendsto
      (let h₁ := explicitFormulaFamilyAnalyticPackage_of_admissible f F₁ hSchedule₁
       fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F₁.toContourFamily.rectangle (h₁.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F₁.toContourFamily.rectangle (h₁.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) ∧
    (Tendsto
      (let h₂ := explicitFormulaFamilyAnalyticPackage_of_admissible f F₂ hSchedule₂
       fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F₂.toContourFamily.rectangle (h₂.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F₂.toContourFamily.rectangle (h₂.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) := by
  constructor
  · exact
      zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
        f F₁ hSchedule₁
  · exact
      zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
        f F₂ hSchedule₂

/-- Owner vertical-boundary remainder theorem.

This is the algebraic remainder form of the vertical decomposition theorem. -/
theorem zetaCompletedExplicitFormulaVerticalBoundaryRemainder_tendsto_zero_ownerVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaRightLineIntegral f
              (F.toContourFamily.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.toContourFamily.rectangle (h.height_schedule.height u)))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
      f F hSchedule
  have hconst :
      Tendsto
        (fun _u : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u)) -
              zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u))) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic f -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hvertical.sub hconst
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f -
          zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        0 := by
    exact sub_self _
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaVerticalBoundaryRemainder f F.toContourFamily
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaRightLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u)) -
              zetaCompletedExplicitFormulaLeftLineIntegral f
                (F.toContourFamily.rectangle (h.height_schedule.height u))) -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
    funext u
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaRightLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u)) -
                zetaCompletedExplicitFormulaLeftLineIntegral f
                  (F.toContourFamily.rectangle (h.height_schedule.height u))) -
              zetaCompletedExplicitFormulaBoundarySumAnalytic f)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- Owner vertical-channel decomposition limit.

This is the vertical-line integration theorem for the completed negative log-derivative
decomposition: the right-minus-left vertical contour contribution converges to the analytic
prime/archimedean/correction boundary sum. -/
theorem zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_ownerVerticalDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    Tendsto
      (let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
       fun u : ℝ =>
        zetaCompletedExplicitFormulaRightLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) -
          zetaCompletedExplicitFormulaLeftLineIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  exact
    zetaCompletedExplicitFormulaVerticalDifference_tendsto_boundarySum_core_ownerVerticalDecomposition
      f F hSchedule

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
