import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContourBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledHorizontalDifferences

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The scheduled inverse-quadratic tail weight tends to zero on any cofinal
height schedule. -/
theorem zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (M : ℝ) :
    Tendsto
      (fun u : ℝ =>
        M * (1 + ‖(F.rectangle (hSchedule.height u)).T‖) ^ (-(2 : ℤ)))
      atTop
      (𝓝 0) := by
  have hheight_norm :
      Tendsto
        (fun u : ℝ => ‖(F.rectangle (hSchedule.height u)).T‖)
        atTop
        atTop :=
    tendsto_norm_atTop_atTop.comp hSchedule.cofinal
  have hheight_norm_plus_one :
      Tendsto
        (fun u : ℝ => 1 + ‖(F.rectangle (hSchedule.height u)).T‖)
        atTop
        atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) hheight_norm
  have hexponent_negative : (-(2 : ℤ)) < 0 :=
    Int.negSucc_lt_zero 1
  have hinverse_quadratic :
      Tendsto
        (fun u : ℝ =>
          (1 + ‖(F.rectangle (hSchedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 0) :=
    (tendsto_zpow_atTop_zero hexponent_negative).comp
      hheight_norm_plus_one
  have hscaled :
      Tendsto
        (fun u : ℝ =>
          M * (1 + ‖(F.rectangle (hSchedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 (M * 0)) :=
    hinverse_quadratic.const_mul M
  have hzero : M * 0 = 0 :=
    mul_zero M
  exact hzero ▸ hscaled

/-- A pointwise bound on the top `s = 1` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral_norm_le_of_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- A pointwise bound on the bottom `s = 1` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral_norm_le_of_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- The top horizontal `s = 1` pole denominator is separated once the rectangle
height has norm at least one. -/
theorem zetaCompletedExplicitFormulaTopPath_onePoleInv_norm_le_one_of_one_le_height
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1
  have him_le_norm : ‖(F.rectangle T).T‖ ≤ ‖z‖ := by
    have him_abs_le : |z.im| ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    have him_norm_le : ‖z.im‖ ≤ ‖z‖ := by
      calc
        ‖z.im‖ = |z.im| := by
          exact Real.norm_eq_abs z.im
        _ ≤ Complex.abs z := him_abs_le
        _ = ‖z‖ := by
          exact (Complex.norm_eq_abs z).symm
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ := by
      calc
        ‖z.im‖ =
            ‖(zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).im‖ := by
          exact congrArg norm
            (Eq.trans
              (Complex.sub_im
                (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) (1 : ℂ))
              (Eq.trans
                (congrArg
                  (fun y : ℝ =>
                    (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).im - y)
                  Complex.one_im)
                (sub_zero
                  (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).im)))
        _ = ‖(F.rectangle T).T‖ :=
          zetaCompletedExplicitFormulaTopPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hdiv :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖(-1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (-1 : ℂ) z
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) (norm_neg (1 : ℂ))
      _ = 1 / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) norm_one
  have hdiv_le : 1 / ‖z‖ ≤ 1 := by
    calc
      1 / ‖z‖ ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le zero_lt_one hone_le_norm
      _ = 1 := by
        exact div_one (1 : ℝ)
  exact Eq.subst
    (motive := fun q : ℝ => q ≤ 1)
    hdiv.symm
    hdiv_le

/-- The bottom horizontal `s = 1` pole denominator is separated once the rectangle
height has norm at least one. -/
theorem zetaCompletedExplicitFormulaBottomPath_onePoleInv_norm_le_one_of_one_le_height
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1
  have him_le_norm : ‖(F.rectangle T).T‖ ≤ ‖z‖ := by
    have him_abs_le : |z.im| ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    have him_norm_le : ‖z.im‖ ≤ ‖z‖ := by
      calc
        ‖z.im‖ = |z.im| := by
          exact Real.norm_eq_abs z.im
        _ ≤ Complex.abs z := him_abs_le
        _ = ‖z‖ := by
          exact (Complex.norm_eq_abs z).symm
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ := by
      calc
        ‖z.im‖ =
            ‖(zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).im‖ := by
          exact congrArg norm
            (Eq.trans
              (Complex.sub_im
                (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) (1 : ℂ))
              (Eq.trans
                (congrArg
                  (fun y : ℝ =>
                    (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).im - y)
                  Complex.one_im)
                (sub_zero
                  (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).im)))
        _ = ‖(F.rectangle T).T‖ :=
          zetaCompletedExplicitFormulaBottomPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hdiv :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖(-1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (-1 : ℂ) z
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) (norm_neg (1 : ℂ))
      _ = 1 / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) norm_one
  have hdiv_le : 1 / ‖z‖ ≤ 1 := by
    calc
      1 / ‖z‖ ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le zero_lt_one hone_le_norm
      _ = 1 := by
        exact div_one (1 : ℝ)
  exact Eq.subst
    (motive := fun q : ℝ => q ≤ 1)
    hdiv.symm
    hdiv_le

/-- Pointwise top-edge decay for the isolated `s = 1` horizontal integrand once
the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_of_nonneg_right hinv (norm_nonneg b)
      _ = ‖b‖ := by
        exact one_mul ‖b‖
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaTopPath_shift_re_mem_uIcc_bounds
      (F.rectangle T) x hx
  have hphi :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaTopPath_shift_im_norm (F.rectangle T) x))
  exact le_trans hproduct hphi

/-- Pointwise bottom-edge decay for the isolated `s = 1` horizontal integrand once
the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_of_nonneg_right hinv (norm_nonneg b)
      _ = ‖b‖ := by
        exact one_mul ‖b‖
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaBottomPath_shift_re_mem_uIcc_bounds
      (F.rectangle T) x hx
  have hphi :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaBottomPath_shift_im_norm (F.rectangle T) x))
  exact le_trans hproduct hphi

/-- Top `s = 1` horizontal edge bound obtained from denominator separation and
`Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral_norm_le_of_pointwise
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
          f hPhi F T x hx (hinv x hx) N)

/-- Bottom `s = 1` horizontal edge bound obtained from denominator separation and
`Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral_norm_le_of_pointwise
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
          f hPhi F T x hx (hinv x hx) N)

/-- Isolated scheduled `s = 1` horizontal remainder bound from the two
single-pole horizontal edge estimates. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 1 ≤ ‖(F.rectangle (h.height_schedule.height u)).T‖)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c +
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  let T : ℝ := h.height_schedule.height u
  let C : ℝ :=
    hPhi.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) N *
    (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))
  have htop :
      ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
      f hPhi F T
      (fun x hx =>
        zetaCompletedExplicitFormulaTopPath_onePoleInv_norm_le_one_of_one_le_height
          F T x hT)
      N
  have hbottom :
      ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
      f hPhi F T
      (fun x hx =>
        zetaCompletedExplicitFormulaBottomPath_onePoleInv_norm_le_one_of_one_le_height
          F T x hT)
      N
  have hedges :
      ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
        ≤
          ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖ +
          ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_norm_le_edges
      f F h u
  have hsum :
      ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖ +
        ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c + C * horizontalEdgeLength F.c :=
    add_le_add htop hbottom
  exact le_trans hedges hsum

/-- The isolated scheduled `s = 1` horizontal remainder is eventually bounded by
an inverse-quadratic height envelope. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    let C : ℝ :=
      h.phi_control.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) 2
    let L : ℝ := horizontalEdgeLength F.c
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  change
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  exact
    (h.height_schedule.eventually_one_le_rectangle_height_norm).mono
      (fun u hT =>
        let q : ℝ :=
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
        have hraw :
            ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u‖
              ≤ C * q * L + C * q * L :=
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height
            f h.phi_control F h u hT 2
        have hedge :
            C * q * L = C * L * q := by
          calc
            C * q * L = (C * q) * L := by
              rfl
            _ = C * (q * L) := by
              exact mul_assoc C q L
            _ = C * (L * q) := by
              exact congrArg (fun x : ℝ => C * x) (mul_comm q L)
            _ = C * L * q := by
              exact (mul_assoc C L q).symm
        have hsum :
            C * q * L + C * q * L = (C * L + C * L) * q := by
          calc
            C * q * L + C * q * L = C * L * q + C * L * q := by
              exact congrArg₂ (fun x y : ℝ => x + y) hedge hedge
            _ = (C * L + C * L) * q := by
              exact (add_mul (C * L) (C * L) q).symm
        Eq.subst
          (motive := fun x : ℝ =>
            ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u‖ ≤ x)
          hsum
          hraw)

/-- Positive-constant form of the isolated scheduled `s = 1` horizontal
inverse-quadratic estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic_pos
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  let B₀ : ℝ := C * L + C * L
  refine ⟨B₀ + 1, add_pos_of_nonneg_of_pos ?_ zero_lt_one, ?_⟩
  · have hC_nonneg : 0 ≤ C :=
      le_of_lt
        (h.phi_control.verticalStripRapidDecayConstant_pos
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) 2)
    have hL_nonneg : 0 ≤ L := by
      exact abs_nonneg ((1 - F.c) - F.c)
    exact add_nonneg
      (mul_nonneg hC_nonneg hL_nonneg)
      (mul_nonneg hC_nonneg hL_nonneg)
  · have hbase :
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
            ≤ B₀ *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
      zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
        f F h
    exact hbase.mono
      (fun u hu =>
        let q : ℝ :=
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
        have hq_nonneg : 0 ≤ q :=
          le_of_lt
            (zpow_pos
              (one_add_norm_pos
                (F.rectangle (h.height_schedule.height u)).T)
              (-(2 : ℤ)))
        have hB_le : B₀ ≤ B₀ + 1 :=
          le_add_of_nonneg_right zero_le_one
        have htail : B₀ * q ≤ (B₀ + 1) * q :=
          mul_le_mul_of_nonneg_right hB_le hq_nonneg
        le_trans hu htail)

/-- The isolated scheduled `s = 1` horizontal remainder tends to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u)
      atTop
      (𝓝 0) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  have hbound :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
          ≤ (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
      f F h
  have hmajorant :
      Tendsto
        (fun u : ℝ =>
          (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
      F h.height_schedule (C * L + C * L)
  exact squeeze_zero_norm' hbound hmajorant

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
