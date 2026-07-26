import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledLogDerivControl
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledConcreteLogDerivControl

/-!
# Scheduled horizontal edge bounds

This file owns the horizontal-edge decay theorem that only needs the scheduled
horizontal log-derivative package.  It avoids asking for global polynomial
control on every zero-excised carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The scheduled horizontal edge product constant with separated exponents. -/
def horizontalScheduledEdgeIntegrandBoundConstantSplit
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (logN phiN : ℕ) (T : ℝ) : ℝ :=
  hLog.bound_constant logN *
    (1 + ‖T‖) ^ logN *
    hPhi.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2)
      phiN *
    (1 + ‖T‖) ^ (-(phiN : ℤ))

/-- A scheduled log-derivative bound after substituting the horizontal height. -/
theorem completedZetaNegLogDeriv_scheduled_height_bound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hLog :
      ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (t : ℝ) (z : ℂ) (N : ℕ)
    (hz : z ∈ hLog.carrier.carrier)
    (hpath : ‖z.im‖ = ‖t‖) :
    ‖completedZetaNegLogDeriv z‖ ≤
      hLog.bound_constant N * (1 + ‖t‖) ^ N :=
  (hLog.bound_of_mem N z hz).trans_eq
    (congrArg
      (fun y : ℝ => hLog.bound_constant N * (1 + y) ^ N)
      hpath)

/-- The scheduled log-derivative target is nonnegative. -/
theorem completedZetaNegLogDeriv_scheduled_height_target_nonneg
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hLog :
      ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (t : ℝ) (N : ℕ) :
    0 ≤ hLog.bound_constant N * (1 + ‖t‖) ^ N :=
  stripConstant_mul_pow_nonneg (hLog.boundConstant_pos N)

/-- The scheduled product estimate for horizontal contour points. -/
theorem zetaCompletedExplicitFormulaContourIntegrand_scheduledStripProduct_bound_split
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (t : ℝ) (z : ℂ) (logN phiN : ℕ)
    (hz : z ∈ hLog.carrier.carrier)
    (hshift :
      min F.c (1 - F.c) - 1 / 2 ≤ (z - 1 / 2 : ℂ).re ∧
        (z - 1 / 2 : ℂ).re ≤ max F.c (1 - F.c) - 1 / 2)
    (hpath : ‖z.im‖ = ‖t‖)
    (hshiftPath : ‖(z - 1 / 2 : ℂ).im‖ = ‖t‖) :
    ‖completedZetaNegLogDeriv z‖ *
        ‖zetaCompletedExplicitFormulaPhi f (z - 1 / 2)‖
      ≤ horizontalScheduledEdgeIntegrandBoundConstantSplit
          hPhi hLog logN phiN t :=
  (norm_product_le_of_bounds
    (completedZetaNegLogDeriv_scheduled_height_bound
      hLog t z logN hz hpath)
    (zetaCompletedExplicitFormulaPhi_strip_height_bound
      hPhi
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2)
      t z phiN hshift hshiftPath)
    (completedZetaNegLogDeriv_scheduled_height_target_nonneg hLog t logN)
    (norm_nonneg (zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))).trans_eq
      (horizontalProductTarget_reassociate
        (hLog.bound_constant logN)
        ((1 + ‖t‖) ^ logN)
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2)
          phiN)
        ((1 + ‖t‖) ^ (-(phiN : ℤ))))

/-- A scheduled pointwise bound on the top horizontal edge. -/
theorem zetaCompletedExplicitFormulaTopEdgeContourIntegrand_scheduled_bound_split
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (logN phiN : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x)‖
      ≤ horizontalScheduledEdgeIntegrandBoundConstantSplit
          hPhi hLog logN phiN (heightSchedule.height u) :=
  (norm_zetaCompletedExplicitFormulaContourIntegrand_le f
    (zetaCompletedExplicitFormulaTopPath
      (F.rectangle (heightSchedule.height u)) x)).trans
    (zetaCompletedExplicitFormulaContourIntegrand_scheduledStripProduct_bound_split
      hPhi hLog (heightSchedule.height u)
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (heightSchedule.height u)) x)
      logN phiN
      (hLog.top_mem u x hx)
      (zetaCompletedExplicitFormulaTopPath_shift_re_mem_uIcc_bounds
        (F.rectangle (heightSchedule.height u)) x hx)
      (zetaCompletedExplicitFormulaTopPath_im_norm
        (F.rectangle (heightSchedule.height u)) x)
      (zetaCompletedExplicitFormulaTopPath_shift_im_norm
        (F.rectangle (heightSchedule.height u)) x))

/-- A scheduled pointwise bound on the bottom horizontal edge. -/
theorem zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_scheduled_bound_split
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (logN phiN : ℕ) :
    ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x)‖
      ≤ horizontalScheduledEdgeIntegrandBoundConstantSplit
          hPhi hLog logN phiN (heightSchedule.height u) :=
  (norm_zetaCompletedExplicitFormulaContourIntegrand_le f
    (zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (heightSchedule.height u)) x)).trans
    (zetaCompletedExplicitFormulaContourIntegrand_scheduledStripProduct_bound_split
      hPhi hLog (heightSchedule.height u)
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (heightSchedule.height u)) x)
      logN phiN
      (hLog.bottom_mem u x hx)
      (zetaCompletedExplicitFormulaBottomPath_shift_re_mem_uIcc_bounds
        (F.rectangle (heightSchedule.height u)) x hx)
      (zetaCompletedExplicitFormulaBottomPath_im_norm
        (F.rectangle (heightSchedule.height u)) x)
      (zetaCompletedExplicitFormulaBottomPath_shift_im_norm
        (F.rectangle (heightSchedule.height u)) x))

/-- The scheduled top horizontal integral is bounded by the scheduled envelope. -/
theorem zetaCompletedExplicitFormulaTopLineIntegral_scheduled_norm_le_envelopeSplit
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (logN phiN : ℕ) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f
        (F.rectangle (heightSchedule.height u))‖
      ≤ horizontalScheduledEdgeIntegrandBoundConstantSplit
          hPhi hLog logN phiN (heightSchedule.height u) *
        horizontalEdgeLength F.c :=
  norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (heightSchedule.height u)) x))
    F.c
    (horizontalScheduledEdgeIntegrandBoundConstantSplit
      hPhi hLog logN phiN (heightSchedule.height u))
    (fun x hx =>
      zetaCompletedExplicitFormulaTopEdgeContourIntegrand_scheduled_bound_split
        hPhi hLog u x hx logN phiN)

/-- The scheduled bottom horizontal integral is bounded by the scheduled envelope. -/
theorem zetaCompletedExplicitFormulaBottomLineIntegral_scheduled_norm_le_envelopeSplit
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog :
      ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (logN phiN : ℕ) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaBottomLineIntegral f
        (F.rectangle (heightSchedule.height u))‖
      ≤ horizontalScheduledEdgeIntegrandBoundConstantSplit
          hPhi hLog logN phiN (heightSchedule.height u) *
        horizontalEdgeLength F.c :=
  norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
    (fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (heightSchedule.height u)) x))
    F.c
    (horizontalScheduledEdgeIntegrandBoundConstantSplit
      hPhi hLog logN phiN (heightSchedule.height u))
    (fun x hx =>
      zetaCompletedExplicitFormulaBottomEdgeContourIntegrand_scheduled_bound_split
        hPhi hLog u x hx logN phiN)

/-- The scheduled horizontal difference envelope. -/
def horizontalScheduledFamilyDifferenceEnvelopeSplit
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (logN phiN : ℕ) (T : ℝ) : ℝ :=
  horizontalScheduledEdgeIntegrandBoundConstantSplit
      h.phi_control h.horizontal_logderiv_control logN phiN T *
    horizontalEdgeLength F.c +
  horizontalScheduledEdgeIntegrandBoundConstantSplit
      h.phi_control h.horizontal_logderiv_control logN phiN T *
    horizontalEdgeLength F.c

/-- The scheduled horizontal difference is bounded by the scheduled envelope. -/
theorem zetaCompletedExplicitFormulaHorizontalDifference_norm_le_scheduledEnvelopeSplit
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (logN phiN : ℕ) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaTopLineIntegral f
          (F.rectangle (h.height_schedule.height u)) -
        zetaCompletedExplicitFormulaBottomLineIntegral f
          (F.rectangle (h.height_schedule.height u))‖
      ≤ horizontalScheduledFamilyDifferenceEnvelopeSplit
          h logN phiN (h.height_schedule.height u) :=
  (norm_sub_le
    (zetaCompletedExplicitFormulaTopLineIntegral f
      (F.rectangle (h.height_schedule.height u)))
    (zetaCompletedExplicitFormulaBottomLineIntegral f
      (F.rectangle (h.height_schedule.height u)))).trans
      (add_le_add
        (zetaCompletedExplicitFormulaTopLineIntegral_scheduled_norm_le_envelopeSplit
          h.phi_control h.horizontal_logderiv_control logN phiN u)
        (zetaCompletedExplicitFormulaBottomLineIntegral_scheduled_norm_le_envelopeSplit
          h.phi_control h.horizontal_logderiv_control logN phiN u))

/-- The scheduled split-exponent edge envelope tends to zero when transform decay dominates. -/
theorem horizontalScheduledFamilyEdgeEnvelopeSplit_tendsto_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (logN requestedDecay : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalScheduledEdgeIntegrandBoundConstantSplit
          h.phi_control h.horizontal_logderiv_control logN
          (logN + requestedDecay.succ) T *
        horizontalEdgeLength F.c)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hpow :
      Tendsto
        (fun T : ℝ =>
          (1 + ‖T‖) ^ logN *
            (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ)))
        atTop
        (𝓝 (0 : ℝ)) :=
    one_add_norm_pow_mul_zpow_dominated_tendsto_zero logN requestedDecay
  let C : ℝ :=
    h.horizontal_logderiv_control.bound_constant logN *
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
        (𝓝 (0 : ℝ)) := by
    exact Eq.subst
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
        horizontalScheduledEdgeIntegrandBoundConstantSplit
          h.phi_control h.horizontal_logderiv_control logN
          (logN + requestedDecay.succ) T *
        horizontalEdgeLength F.c) =
        fun T : ℝ =>
          C *
            ((1 + ‖T‖) ^ logN *
              (1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ))) := by
    funext T
    exact horizontalEnvelopeSplit_reassociate
      (h.horizontal_logderiv_control.bound_constant logN)
      (h.phi_control.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2)
        (logN + requestedDecay.succ))
      (horizontalEdgeLength F.c)
      ((1 + ‖T‖) ^ logN)
      ((1 + ‖T‖) ^ (-(logN + requestedDecay.succ : ℤ)))
  exact hrewrite ▸ hscaled

/-- The scheduled split-exponent difference envelope tends to zero. -/
theorem horizontalScheduledFamilyDifferenceEnvelopeSplit_tendsto_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (logN requestedDecay : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalScheduledFamilyDifferenceEnvelopeSplit
          h logN (logN + requestedDecay.succ) T)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hedge :
      Tendsto
        (fun T : ℝ =>
          horizontalScheduledEdgeIntegrandBoundConstantSplit
            h.phi_control h.horizontal_logderiv_control logN
            (logN + requestedDecay.succ) T *
          horizontalEdgeLength F.c)
        atTop
        (𝓝 (0 : ℝ)) :=
    horizontalScheduledFamilyEdgeEnvelopeSplit_tendsto_zero h logN requestedDecay
  have hsum :
      Tendsto
        (fun T : ℝ =>
          horizontalScheduledEdgeIntegrandBoundConstantSplit
              h.phi_control h.horizontal_logderiv_control logN
              (logN + requestedDecay.succ) T *
            horizontalEdgeLength F.c +
          horizontalScheduledEdgeIntegrandBoundConstantSplit
              h.phi_control h.horizontal_logderiv_control logN
              (logN + requestedDecay.succ) T *
            horizontalEdgeLength F.c)
        atTop
        (𝓝 ((0 : ℝ) + 0)) :=
    hedge.add hedge
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun T : ℝ =>
            horizontalScheduledEdgeIntegrandBoundConstantSplit
                h.phi_control h.horizontal_logderiv_control logN
                (logN + requestedDecay.succ) T *
              horizontalEdgeLength F.c +
            horizontalScheduledEdgeIntegrandBoundConstantSplit
                h.phi_control h.horizontal_logderiv_control logN
                (logN + requestedDecay.succ) T *
              horizontalEdgeLength F.c)
          atTop
          (𝓝 x))
      (zero_add 0)
      hsum

/-- The scheduled horizontal difference tends to zero along the stored height schedule. -/
theorem zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero_of_scheduledPackage
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (logN : ℕ) :
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
        zetaCompletedExplicitFormulaHorizontalDifference_norm_le_scheduledEnvelopeSplit
          h logN (logN + logN.succ) u))
    ((horizontalScheduledFamilyDifferenceEnvelopeSplit_tendsto_zero h logN logN).comp
      h.height_schedule.cofinal)

/-- The horizontal-side contribution determined only by a scheduled analytic package. -/
noncomputable def explicitFormulaScheduledPackageHorizontalSideDifference
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f
      (F.rectangle (h.height_schedule.height u)) -
    zetaCompletedExplicitFormulaBottomLineIntegral f
      (F.rectangle (h.height_schedule.height u))

/-- Scheduled package horizontal-side decay, exported under the side-difference name. -/
theorem explicitFormulaScheduledPackageHorizontalSideDifference_tendsto_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (logN : ℕ) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledPackageHorizontalSideDifference h u)
      atTop
      (𝓝 (0 : ℂ)) :=
  zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero_of_scheduledPackage
    h logN

/-- Concrete separated zeta-side and inverse-Gamma bounds on the scheduled carrier
give horizontal-side decay along the scheduled rectangles. -/
theorem zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero_of_concreteFactorData
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
    (zetaData :
      CompletedZetaZeroExcisedStrip.ZetaSideBoundData carrier)
    (gammaData :
      CompletedZetaZeroExcisedStrip.InverseGammaBoundData carrier)
    (logN : ℕ) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f
            (F.rectangle (heightSchedule.height u)) -
          zetaCompletedExplicitFormulaBottomLineIntegral f
            (F.rectangle (heightSchedule.height u)))
      atTop
      (𝓝 (0 : ℂ)) :=
  zetaCompletedExplicitFormulaHorizontalDifference_tendsto_zero_of_scheduledPackage
    (ExplicitFormulaScheduledFamilyAnalyticPackage.ofConcreteZetaSideAndGammaBoundData
      phiControl heightSchedule carrier topMem bottomMem zetaData gammaData)
    logN

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
