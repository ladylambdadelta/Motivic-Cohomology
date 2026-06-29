import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContourBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaResidueRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaNormalizationBridge.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.ZetaCompletedLogDerivativeCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaLogDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.Owner
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
# Explicit-formula horizontal decay

This owner layer contains horizontal edge estimates and horizontal residue-window decay.
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
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (T : ℝ)
    (hTopMem :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    ‖∫ x in Set.uIcc F.c (1 - F.c),
        zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstant
          h.phi_control h.logderiv_control (F.rectangle T) E N *
        horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaTopLineIntegral_uIcc_norm_le_envelope
      h.phi_control h.logderiv_control (F.rectangle T) E hTopMem N

/-- The interval-integral estimate packaged with the contour-family bottom path. -/
theorem horizontalBottomLineIntegral_norm_le_constant
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (T : ℝ)
    (hBottomMem :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    ‖∫ x in Set.uIcc F.c (1 - F.c),
        zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)‖
      ≤ horizontalUnorderedEdgeIntegrandBoundConstant
          h.phi_control h.logderiv_control (F.rectangle T) E N *
        horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaBottomLineIntegral_uIcc_norm_le_envelope
      h.phi_control h.logderiv_control (F.rectangle T) E hBottomMem N

/-- A horizontal line integral along a contour family is bounded by the explicit edge constant.
This packages the pointwise contour estimate with the interval-length estimate in one place. -/
theorem horizontalLineIntegral_norm_le_contourBound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (T : ℝ)
    (hTopMem :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ ≤
      horizontalUnorderedEdgeIntegrandBoundConstant
          h.phi_control h.logderiv_control (F.rectangle T) E N *
        horizontalEdgeLength F.c :=
  horizontalTopLineIntegral_norm_le_constant h E T hTopMem N

/-- The bottom horizontal line integral is bounded by the explicit edge constant. -/
theorem horizontalLineIntegral_norm_le_contourBound_bottom
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (T : ℝ)
    (hBottomMem :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖ ≤
      horizontalUnorderedEdgeIntegrandBoundConstant
          h.phi_control h.logderiv_control (F.rectangle T) E N *
        horizontalEdgeLength F.c :=
  horizontalBottomLineIntegral_norm_le_constant h E T hBottomMem N

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
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (E : CompletedZetaZeroExcisedStrip
      (min h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c))
      (max h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c)))
    (hTopMem :
      ∀ x : ℝ, x ∈ Set.uIcc h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c) →
        zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x ∈ E.carrier)
    (N : ℕ) :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaTopLineIntegral f h.contour_data.rectangle‖ ≤ C :=
  ⟨horizontalUnorderedEdgeIntegrandBoundConstant
      h.phi_control h.logderiv_control h.contour_data.rectangle E N *
      horizontalEdgeLength h.contour_data.rectangle.c,
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x))
      h.contour_data.rectangle.c
      (horizontalUnorderedEdgeIntegrandBoundConstant
        h.phi_control h.logderiv_control h.contour_data.rectangle E N)
      (fun x hx =>
        zetaCompletedExplicitFormulaTopEdgeContourIntegrand_uIcc_bound
          h.phi_control h.logderiv_control h.contour_data.rectangle E x hx N
          (hTopMem x hx))⟩

/-- The single-rectangle bottom horizontal integral is bounded by the unordered edge constant. -/
theorem horizontalBottomIntegral_norm_le_uniformContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (E : CompletedZetaZeroExcisedStrip
      (min h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c))
      (max h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c)))
    (hBottomMem :
      ∀ x : ℝ, x ∈ Set.uIcc h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c) →
        zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x ∈ E.carrier)
    (N : ℕ) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaBottomLineIntegral f h.contour_data.rectangle‖ ≤ C :=
  ⟨horizontalUnorderedEdgeIntegrandBoundConstant
      h.phi_control h.logderiv_control h.contour_data.rectangle E N *
      horizontalEdgeLength h.contour_data.rectangle.c,
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x))
      h.contour_data.rectangle.c
      (horizontalUnorderedEdgeIntegrandBoundConstant
        h.phi_control h.logderiv_control h.contour_data.rectangle E N)
      (fun x hx =>
        zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_uIcc_bound
          h.phi_control h.logderiv_control h.contour_data.rectangle E x hx N
          (hBottomMem x hx))⟩

/-- A norm bound for a difference follows from separate bounds on its two terms. -/
theorem norm_sub_le_add_of_norm_bounds {a b : ℂ} {A B : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖a - b‖ ≤ A + B :=
  (norm_sub_le a b).trans (add_le_add ha hb)

/-- The horizontal difference of the top and bottom integrals is bounded by twice the uniform
edge constant times the interval length. -/
theorem horizontalDifference_norm_le_uniformContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (E : CompletedZetaZeroExcisedStrip
      (min h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c))
      (max h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c)))
    (hTopMem :
      ∀ x : ℝ, x ∈ Set.uIcc h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c) →
        zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x ∈ E.carrier)
    (hBottomMem :
      ∀ x : ℝ, x ∈ Set.uIcc h.contour_data.rectangle.c (1 - h.contour_data.rectangle.c) →
        zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x ∈ E.carrier)
    (N : ℕ) :
    ∃ C : ℝ,
      ‖zetaHorizontalIntegralTop f h.contour_data.rectangle -
        zetaHorizontalIntegralBottom f h.contour_data.rectangle‖ ≤ C := by
  match horizontalIntegral_norm_le_uniformContourBound h E hTopMem N,
      horizontalBottomIntegral_norm_le_uniformContourBound h E hBottomMem N with
  | ⟨Ctop, htop⟩, ⟨Cbot, hbot⟩ =>
      exact ⟨Ctop + Cbot, norm_sub_le_add_of_norm_bounds htop hbot⟩

/-- The top horizontal line integral in a contour family is bounded by the uniform family edge
bound times the horizontal length. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topLineIntegral_norm_le_core
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (T : ℝ)
    (hTopMem :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ ≤ C :=
  ⟨horizontalUnorderedEdgeIntegrandBoundConstant
      h.phi_control h.logderiv_control (F.rectangle T) E N *
      horizontalEdgeLength F.c,
    horizontalLineIntegral_norm_le_contourBound h E T hTopMem N⟩

/-- Thin wrapper for the top horizontal line integral estimate. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topLineIntegral_norm_le
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (T : ℝ)
    (hTopMem :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ ≤ C :=
  h.topLineIntegral_norm_le_core E T hTopMem N

/-- The shared decay envelope controlling the horizontal family estimates. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecayEnvelope_core
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalUnorderedFamilyDifferenceEnvelopeSplit
          h.phi_control h.logderiv_control F E N (N + N.succ) T)
      atTop (𝓝 (0 : ℝ)) := by
  exact horizontalUnorderedFamilyDifferenceEnvelopeSplit_tendsto_zero
    h.phi_control h.logderiv_control F E N N

/-- Thin wrapper for the horizontal decay envelope. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecayEnvelope
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalUnorderedFamilyDifferenceEnvelopeSplit
          h.phi_control h.logderiv_control F E N (N + N.succ) T)
      atTop (𝓝 (0 : ℝ)) :=
  h.horizontalDecayEnvelope_core E N

/-- The horizontal top-minus-bottom difference tends to zero along a contour family. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecay_core
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      atTop
      (𝓝 (0 : ℂ)) :=
  zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero
    h.phi_control h.logderiv_control F E hTopMem hBottomMem N

/-- Thin wrapper for the horizontal decay of the top-minus-bottom difference. -/
theorem ExplicitFormulaFamilyAnalyticPackage.horizontalDecay
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath (F.rectangle T) x ∈ E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      atTop
      (𝓝 (0 : ℂ)) :=
  h.horizontalDecay_core E hTopMem hBottomMem N

/-- A reusable bound for the bottom horizontal line integral in terms of pointwise edge bounds. -/
theorem ExplicitFormulaFamilyAnalyticPackage.bottomLineIntegral_norm_le_core
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (T : ℝ)
    (hBottomMem :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x ∈ E.carrier)
    (N : ℕ) :
    ∃ C : ℝ, ‖zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖ ≤ C :=
  ⟨horizontalUnorderedEdgeIntegrandBoundConstant
      h.phi_control h.logderiv_control (F.rectangle T) E N *
      horizontalEdgeLength F.c,
    horizontalLineIntegral_norm_le_contourBound_bottom h E T hBottomMem N⟩



/-- The analytic package exposes the owner-level reflected-autocorrelation identity. -/
theorem zetaCompletedExplicitFormulaContourBoundary_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.autocorrelation (ZetaAdmissibleFunction.reflect f) =
      ZetaAdmissibleFunction.reflect (ZetaAdmissibleFunction.autocorrelation f) :=
  ZetaAdmissibleFunction.autocorrelation_dagger_eq_reflect f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
