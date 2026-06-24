import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledHorizontalDifferences
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledInverseQuadraticTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContourBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Owner

/-!
# Zero-pole horizontal edge bounds

This file owns the isolated `s = 0` horizontal-edge estimates needed upstream
of the zero-pole Cauchy inversion theorem.  It does not import the one-pole
cancellation stack or the right zero-pole vertical inversion consumers.
-/

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

/-- A pointwise bound on the top `s = 0` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_of_pointwise_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- A pointwise bound on the bottom `s = 0` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_of_pointwise_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- Pointwise top-edge decay for the isolated `s = 0` horizontal integrand once
the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_right (norm_nonneg b) hinv
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

/-- Pointwise bottom-edge decay for the isolated `s = 0` horizontal integrand
once the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_right (norm_nonneg b) hinv
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

/-- Top `s = 0` horizontal edge bound obtained from denominator separation and
`Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_of_pointwise_ownerZeroPoleHorizontal
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
          f hPhi F T x hx (hinv x hx) N)

/-- Bottom `s = 0` horizontal edge bound obtained from denominator separation
and `Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_of_pointwise_ownerZeroPoleHorizontal
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
          f hPhi F T x hx (hinv x hx) N)

/-- Isolated scheduled `s = 0` horizontal remainder bound from the two
single-pole horizontal edge estimates. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hinvTop :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 /
          zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x‖ ≤ 1)
    (hinvBottom :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 /
          zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
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
      ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
      f hPhi F T hinvTop N
  have hbottom :
      ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
      f hPhi F T hinvBottom N
  have hedges :
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
        ≤
          ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖ +
          ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_edges
      f F h u
  have hsum :
      ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖ +
        ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c + C * horizontalEdgeLength F.c :=
    add_le_add htop hbottom
  exact le_trans hedges hsum

/-- The top horizontal `s = 0` pole denominator is separated once the rectangle
height has norm at least one. -/
theorem zetaCompletedExplicitFormulaTopPath_zeroPoleInv_norm_le_one_of_one_le_height_ownerZeroPoleHorizontal
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaTopPath (F.rectangle T) x
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
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ :=
      zetaCompletedExplicitFormulaTopPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le zero_lt_one hone_le_norm
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

/-- The bottom horizontal `s = 0` pole denominator is separated once the
rectangle height has norm at least one. -/
theorem zetaCompletedExplicitFormulaBottomPath_zeroPoleInv_norm_le_one_of_one_le_height_ownerZeroPoleHorizontal
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x
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
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ :=
      zetaCompletedExplicitFormulaBottomPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le zero_lt_one hone_le_norm
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

/-- Scheduled isolated `s = 0` horizontal remainder bound at heights where the
horizontal pole denominators are separated by the height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 1 ≤ ‖(F.rectangle (h.height_schedule.height u)).T‖)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
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
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_inv_le_one_ownerZeroPoleHorizontal
      f hPhi F h u
      (fun x hx =>
        zetaCompletedExplicitFormulaTopPath_zeroPoleInv_norm_le_one_of_one_le_height_ownerZeroPoleHorizontal
          F (h.height_schedule.height u) x hT)
      (fun x hx =>
        zetaCompletedExplicitFormulaBottomPath_zeroPoleInv_norm_le_one_of_one_le_height_ownerZeroPoleHorizontal
          F (h.height_schedule.height u) x hT)
      N

/-- The isolated scheduled `s = 0` horizontal remainder is eventually bounded
by an inverse-quadratic height envelope. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    let C : ℝ :=
      h.phi_control.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) 2
    let L : ℝ := horizontalEdgeLength F.c
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  change
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  exact
    (h.height_schedule.eventually_one_le_rectangle_height_norm).mono
      (fun u hT =>
        let q : ℝ :=
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
        have hraw :
            ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u‖
              ≤ C * q * L + C * q * L :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height_ownerZeroPoleHorizontal
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
            ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u‖ ≤ x)
          hsum
          hraw)

/-- The isolated scheduled `s = 0` horizontal remainder tends to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u)
      atTop
      (𝓝 0) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  have hbound :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
          ≤ (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic_ownerZeroPoleHorizontal
      f F h
  have hmajorant :
      Tendsto
        (fun u : ℝ =>
          (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero_ownerShared
      F h.height_schedule (C * L + C * L)
  exact squeeze_zero_norm' hbound hmajorant

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
