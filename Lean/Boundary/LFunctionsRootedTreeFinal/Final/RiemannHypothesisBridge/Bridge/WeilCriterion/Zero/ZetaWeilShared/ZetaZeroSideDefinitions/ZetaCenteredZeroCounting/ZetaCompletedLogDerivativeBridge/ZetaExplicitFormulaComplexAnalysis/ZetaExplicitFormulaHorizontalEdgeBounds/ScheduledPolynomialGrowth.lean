import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Scheduled
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.PolynomialGrowthControl

/-!
# Scheduled horizontal bounds from fixed-degree log-derivative growth

This file owns the scheduled horizontal decay theorem whose logarithmic
derivative input is fixed-degree polynomial growth on the scheduled carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

structure ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (heightSchedule : ExplicitFormulaCofinalHeightSchedule F) where
  carrier :
    CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c))
  top_mem :
    ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      zetaCompletedExplicitFormulaTopPath
        (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier
  bottom_mem :
    ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier
  growth_degree : ℕ
  bound_constant : ℝ
  bound_constant_pos : 0 < bound_constant
  bound :
    ∀ z : ℂ,
      z ∈ carrier.carrier →
        ‖completedZetaNegLogDeriv z‖ ≤
          bound_constant * (1 + ‖z.im‖) ^ growth_degree

structure ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) where
  phi_control : ZetaPhiAnalyticControl f
  height_schedule : ExplicitFormulaCofinalHeightSchedule F
  horizontal_logderiv_control :
    ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl f F height_schedule

def ExplicitFormulaScheduledHorizontalLogDerivControl.toPolynomialGrowthAtDegree
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (h : ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (N : ℕ) :
    ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl f F heightSchedule :=
  { carrier := h.carrier
    top_mem := h.top_mem
    bottom_mem := h.bottom_mem
    growth_degree := N
    bound_constant := h.bound_constant N
    bound_constant_pos := h.bound_constant_pos N
    bound := fun z hz => h.bound N z hz }

def ExplicitFormulaScheduledFamilyAnalyticPackage.toPolynomialGrowthAtDegree
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (N : ℕ) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F :=
  { phi_control := h.phi_control
    height_schedule := h.height_schedule
    horizontal_logderiv_control :=
      h.horizontal_logderiv_control.toPolynomialGrowthAtDegree N }

def ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl.ofCommonDegreeFactorControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (carrier :
      CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (factorControl : CompletedZetaNegLogDerivCommonDegreeFactorControl) :
    ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl f F heightSchedule :=
  { carrier := carrier
    top_mem := topMem
    bottom_mem := bottomMem
    growth_degree :=
      factorControl.K
        (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier
    bound_constant :=
      factorControl.Czeta
          (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier +
        factorControl.Cgamma
          (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier
    bound_constant_pos :=
      add_pos
        (factorControl.Czeta_pos
          (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier)
        (factorControl.Cgamma_pos
          (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier)
    bound :=
      fun z hz =>
        completedZetaNegLogDeriv_norm_bound_of_factor_bounds
          carrier
          (factorControl.K
            (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier)
          (factorControl.Czeta
            (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier)
          (factorControl.Cgamma
            (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier)
          z hz
          (factorControl.Czeta_bound
            (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier)
          (factorControl.Cgamma_bound
            (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier) }

def ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage.ofCommonDegreeFactorControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (phiControl : ZetaPhiAnalyticControl f)
    (heightSchedule : ExplicitFormulaCofinalHeightSchedule F)
    (carrier :
      CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (topMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (bottomMem :
      ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier)
    (factorControl : CompletedZetaNegLogDerivCommonDegreeFactorControl) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F :=
  { phi_control := phiControl
    height_schedule := heightSchedule
    horizontal_logderiv_control :=
      ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl.ofCommonDegreeFactorControl
        carrier topMem bottomMem factorControl }

theorem ExplicitFormulaFamilyAnalyticPackage.existsPolynomialScheduledPackage_of_polynomialGrowthControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hGrowth : CompletedZetaNegLogDerivPolynomialGrowthControl f) :
    ∃ hPoly : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F,
      hPoly.height_schedule = h.height_schedule :=
  Exists.elim h.scheduled_horizontalFamilyZeroExcisedStrip
    (fun carrier hcarrier =>
      Exists.elim
        (hGrowth.zero_excised_polynomial_growth
          (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier)
        (fun growthDegree hdegree =>
          Exists.elim hdegree
            (fun boundConstant hbound =>
              Exists.intro
                { phi_control := h.phi_control
                  height_schedule := h.height_schedule
                  horizontal_logderiv_control :=
                    { carrier := carrier
                      top_mem := hcarrier.1
                      bottom_mem := hcarrier.2
                      growth_degree := growthDegree
                      bound_constant := boundConstant
                      bound_constant_pos := hbound.1
                      bound := hbound.2 } }
                rfl)))

def horizontalPolynomialScheduledEdgeIntegrandBoundConstant
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
        f F heightSchedule)
    (phiN : ℕ) (T : ℝ) : ℝ :=
  hLog.bound_constant *
    (1 + ‖T‖) ^ hLog.growth_degree *
    hPhi.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2)
      phiN *
    (1 + ‖T‖) ^ (-(phiN : ℤ))

theorem completedZetaNegLogDeriv_polynomialScheduled_height_bound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hLog :
      ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
        f F heightSchedule)
    (t : ℝ) (z : ℂ)
    (hz : z ∈ hLog.carrier.carrier)
    (hpath : ‖z.im‖ = ‖t‖) :
    ‖completedZetaNegLogDeriv z‖ ≤
      hLog.bound_constant * (1 + ‖t‖) ^ hLog.growth_degree :=
  (hLog.bound z hz).trans_eq
    (congrArg
      (fun y : ℝ =>
        hLog.bound_constant * (1 + y) ^ hLog.growth_degree)
      hpath)

theorem completedZetaNegLogDeriv_polynomialScheduled_height_target_nonneg
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hLog :
      ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
        f F heightSchedule)
    (t : ℝ) :
    0 ≤ hLog.bound_constant * (1 + ‖t‖) ^ hLog.growth_degree :=
  stripConstant_mul_pow_nonneg hLog.bound_constant_pos

theorem zetaCompletedExplicitFormulaContourIntegrand_polynomialScheduledStripProduct_bound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
        f F heightSchedule)
    (t : ℝ) (z : ℂ) (phiN : ℕ)
    (hz : z ∈ hLog.carrier.carrier)
    (hshift :
      min F.c (1 - F.c) - 1 / 2 ≤ (z - 1 / 2 : ℂ).re ∧
        (z - 1 / 2 : ℂ).re ≤ max F.c (1 - F.c) - 1 / 2)
    (hpath : ‖z.im‖ = ‖t‖)
    (hshiftPath : ‖(z - 1 / 2 : ℂ).im‖ = ‖t‖) :
    ‖completedZetaNegLogDeriv z‖ *
        ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖
      ≤ horizontalPolynomialScheduledEdgeIntegrandBoundConstant
          hPhi hLog phiN t :=
  (norm_product_le_of_bounds
    (completedZetaNegLogDeriv_polynomialScheduled_height_bound
      hLog t z hz hpath)
    (zetaCompletedExplicitFormulaPhi_strip_height_bound
      hPhi
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2)
      t z phiN hshift hshiftPath)
    (completedZetaNegLogDeriv_polynomialScheduled_height_target_nonneg
      hLog t)
    (norm_nonneg (zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))).trans_eq
      (horizontalProductTarget_reassociate
        hLog.bound_constant
        ((1 + ‖t‖) ^ hLog.growth_degree)
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2)
          phiN)
        ((1 + ‖t‖) ^ (-(phiN : ℤ))))

theorem zetaCompletedExplicitFormulaTopEdgeContourIntegrand_polynomialScheduled_bound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
        f F heightSchedule)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (phiN : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x)‖
      ≤ horizontalPolynomialScheduledEdgeIntegrandBoundConstant
          hPhi hLog phiN (heightSchedule.height u) :=
  (norm_zetaCompletedExplicitFormulaContourIntegrand_le f
    (zetaCompletedExplicitFormulaTopPath
      (F.rectangle (heightSchedule.height u)) x)).trans
    (zetaCompletedExplicitFormulaContourIntegrand_polynomialScheduledStripProduct_bound
      hPhi hLog (heightSchedule.height u)
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (heightSchedule.height u)) x)
      phiN
      (hLog.top_mem u x hx)
      (zetaCompletedExplicitFormulaTopPath_shift_re_mem_uIcc_bounds
        (F.rectangle (heightSchedule.height u)) x hx)
      (zetaCompletedExplicitFormulaTopPath_im_norm
        (F.rectangle (heightSchedule.height u)) x)
      (zetaCompletedExplicitFormulaTopPath_shift_im_norm
        (F.rectangle (heightSchedule.height u)) x))

theorem zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_polynomialScheduled_bound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
        f F heightSchedule)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (phiN : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x)‖
      ≤ horizontalPolynomialScheduledEdgeIntegrandBoundConstant
          hPhi hLog phiN (heightSchedule.height u) :=
  (norm_zetaCompletedExplicitFormulaContourIntegrand_le f
    (zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (heightSchedule.height u)) x)).trans
    (zetaCompletedExplicitFormulaContourIntegrand_polynomialScheduledStripProduct_bound
      hPhi hLog (heightSchedule.height u)
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (heightSchedule.height u)) x)
      phiN
      (hLog.bottom_mem u x hx)
      (zetaCompletedExplicitFormulaBottomPath_shift_re_mem_uIcc_bounds
        (F.rectangle (heightSchedule.height u)) x hx)
      (zetaCompletedExplicitFormulaBottomPath_im_norm
        (F.rectangle (heightSchedule.height u)) x)
      (zetaCompletedExplicitFormulaBottomPath_shift_im_norm
        (F.rectangle (heightSchedule.height u)) x))

theorem zetaCompletedExplicitFormulaTopLineIntegral_polynomialScheduled_norm_le_envelope
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
        f F heightSchedule)
    (phiN : ℕ) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f
        (F.rectangle (heightSchedule.height u))‖
      ≤ horizontalPolynomialScheduledEdgeIntegrandBoundConstant
          hPhi hLog phiN (heightSchedule.height u) *
        horizontalEdgeLength F.c :=
  norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x))
    F.c
    (horizontalPolynomialScheduledEdgeIntegrandBoundConstant
      hPhi hLog phiN (heightSchedule.height u))
    (fun x hx =>
      zetaCompletedExplicitFormulaTopEdgeContourIntegrand_polynomialScheduled_bound
        hPhi hLog u x hx phiN)

theorem zetaCompletedExplicitFormulaBottomLineIntegral_polynomialScheduled_norm_le_envelope
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalPolynomialLogDerivControl
        f F heightSchedule)
    (phiN : ℕ) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaBottomLineIntegral f
        (F.rectangle (heightSchedule.height u))‖
      ≤ horizontalPolynomialScheduledEdgeIntegrandBoundConstant
          hPhi hLog phiN (heightSchedule.height u) *
        horizontalEdgeLength F.c :=
  norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x))
    F.c
    (horizontalPolynomialScheduledEdgeIntegrandBoundConstant
      hPhi hLog phiN (heightSchedule.height u))
    (fun x hx =>
      zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_polynomialScheduled_bound
        hPhi hLog u x hx phiN)

def horizontalPolynomialScheduledFamilyDifferenceEnvelope
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (phiN : ℕ) (T : ℝ) : ℝ :=
  horizontalPolynomialScheduledEdgeIntegrandBoundConstant
      h.phi_control h.horizontal_logderiv_control phiN T *
    horizontalEdgeLength F.c +
  horizontalPolynomialScheduledEdgeIntegrandBoundConstant
      h.phi_control h.horizontal_logderiv_control phiN T *
    horizontalEdgeLength F.c

theorem zetaCompletedExplicitFormulaHorizontalDifference_norm_le_polynomialScheduledEnvelope
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (phiN : ℕ) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f
          (F.rectangle (h.height_schedule.height u)) -
        zetaCompletedExplicitFormulaBottomLineIntegral f
          (F.rectangle (h.height_schedule.height u))‖
      ≤ horizontalPolynomialScheduledFamilyDifferenceEnvelope
          h phiN (h.height_schedule.height u) :=
  (norm_sub_le
    (zetaCompletedExplicitFormulaTopLineIntegral f
      (F.rectangle (h.height_schedule.height u)))
    (zetaCompletedExplicitFormulaBottomLineIntegral f
      (F.rectangle (h.height_schedule.height u)))).trans
      (add_le_add
        (zetaCompletedExplicitFormulaTopLineIntegral_polynomialScheduled_norm_le_envelope
          h.phi_control h.horizontal_logderiv_control phiN u)
        (zetaCompletedExplicitFormulaBottomLineIntegral_polynomialScheduled_norm_le_envelope
          h.phi_control h.horizontal_logderiv_control phiN u))

theorem horizontalPolynomialScheduledFamilyEdgeEnvelope_tendsto_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (requestedDecay : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalPolynomialScheduledEdgeIntegrandBoundConstant
          h.phi_control h.horizontal_logderiv_control
          (h.horizontal_logderiv_control.growth_degree + requestedDecay.succ) T *
        horizontalEdgeLength F.c)
      atTop
      (𝓝 (0 : ℝ)) := by
  let logN : ℕ := h.horizontal_logderiv_control.growth_degree
  have hpow :
      Tendsto
        (fun T : ℝ =>
          (1 + ‖T‖) ^ logN *
            (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ)))
        atTop
        (𝓝 (0 : ℝ)) :=
    one_add_norm_pow_mul_zpow_dominated_tendsto_zero logN requestedDecay
  let C : ℝ :=
    h.horizontal_logderiv_control.bound_constant *
      h.phi_control.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2)
        (logN + requestedDecay.succ) *
      horizontalEdgeLength F.c
  have hscaled :
      Tendsto
        (fun T : ℝ =>
          C *
            ((1 + ‖T‖) ^ logN *
              (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ))))
        atTop
        (𝓝 (0 : ℝ)) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun T : ℝ =>
            C *
              ((1 + ‖T‖) ^ logN *
                (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ))))
          atTop
          (𝓝 x))
      (mul_zero C)
      (hpow.const_mul C)
  have hrewrite :
      (fun T : ℝ =>
        horizontalPolynomialScheduledEdgeIntegrandBoundConstant
          h.phi_control h.horizontal_logderiv_control
          (h.horizontal_logderiv_control.growth_degree + requestedDecay.succ) T *
        horizontalEdgeLength F.c) =
        fun T : ℝ =>
          C *
            ((1 + ‖T‖) ^ logN *
              (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ))) :=
    funext
      (fun T =>
        horizontalEnvelopeSplit_reassociate
          h.horizontal_logderiv_control.bound_constant
          (h.phi_control.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2)
            (logN + requestedDecay.succ))
          (horizontalEdgeLength F.c)
          ((1 + ‖T‖) ^ logN)
          ((1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ))))
  exact hrewrite ▸ hscaled

theorem horizontalPolynomialScheduledFamilyDifferenceEnvelope_tendsto_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (requestedDecay : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalPolynomialScheduledFamilyDifferenceEnvelope
          h (h.horizontal_logderiv_control.growth_degree + requestedDecay.succ) T)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hedge :
      Tendsto
        (fun T : ℝ =>
          horizontalPolynomialScheduledEdgeIntegrandBoundConstant
            h.phi_control h.horizontal_logderiv_control
            (h.horizontal_logderiv_control.growth_degree + requestedDecay.succ) T *
          horizontalEdgeLength F.c)
        atTop
        (𝓝 (0 : ℝ)) :=
    horizontalPolynomialScheduledFamilyEdgeEnvelope_tendsto_zero h requestedDecay
  have hsum :
      Tendsto
        (fun T : ℝ =>
          horizontalPolynomialScheduledEdgeIntegrandBoundConstant
              h.phi_control h.horizontal_logderiv_control
              (h.horizontal_logderiv_control.growth_degree + requestedDecay.succ) T *
            horizontalEdgeLength F.c +
          horizontalPolynomialScheduledEdgeIntegrandBoundConstant
              h.phi_control h.horizontal_logderiv_control
              (h.horizontal_logderiv_control.growth_degree + requestedDecay.succ) T *
            horizontalEdgeLength F.c)
        atTop
        (𝓝 ((0 : ℝ) + 0)) :=
    hedge.add hedge
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun T : ℝ =>
            horizontalPolynomialScheduledEdgeIntegrandBoundConstant
                h.phi_control h.horizontal_logderiv_control
                (h.horizontal_logderiv_control.growth_degree + requestedDecay.succ) T *
              horizontalEdgeLength F.c +
            horizontalPolynomialScheduledEdgeIntegrandBoundConstant
                h.phi_control h.horizontal_logderiv_control
                (h.horizontal_logderiv_control.growth_degree + requestedDecay.succ) T *
              horizontalEdgeLength F.c)
          atTop
          (𝓝 x))
      (zero_add 0)
      hsum

theorem zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero_of_polynomialScheduledPackage
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f
            (F.rectangle (h.height_schedule.height u)) -
          zetaCompletedExplicitFormulaBottomLineIntegral f
            (F.rectangle (h.height_schedule.height u)))
      atTop
      (𝓝 (0 : ℂ)) :=
  squeeze_zero_norm'
    (Eventually.of_forall
      (fun u =>
        zetaCompletedExplicitFormulaHorizontalDifference_norm_le_polynomialScheduledEnvelope
          h
          (h.horizontal_logderiv_control.growth_degree +
            h.horizontal_logderiv_control.growth_degree.succ)
          u))
    ((horizontalPolynomialScheduledFamilyDifferenceEnvelope_tendsto_zero
      h h.horizontal_logderiv_control.growth_degree).comp
      h.height_schedule.cofinal)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
