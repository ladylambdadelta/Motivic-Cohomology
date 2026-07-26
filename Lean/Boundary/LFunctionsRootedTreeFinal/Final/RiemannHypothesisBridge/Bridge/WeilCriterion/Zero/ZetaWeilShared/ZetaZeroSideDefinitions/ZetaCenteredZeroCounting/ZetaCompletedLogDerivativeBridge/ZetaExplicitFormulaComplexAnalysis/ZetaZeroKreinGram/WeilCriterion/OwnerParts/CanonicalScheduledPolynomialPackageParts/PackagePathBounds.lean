import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.ScheduledPolynomialGrowth

/-!
# Path bounds extracted from polynomial scheduled packages

This file owns the explicit top and bottom completed-log-derivative path bounds
stored in a fixed-degree polynomial scheduled package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The top horizontal path bound stored in a polynomial scheduled package. -/
theorem ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage.topPath_completedZetaNegLogDeriv_bound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ‖completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x)‖ ≤
      h.horizontal_logderiv_control.bound_constant *
        (1 + ‖h.height_schedule.height u‖) ^
          h.horizontal_logderiv_control.growth_degree :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x
  let hz : z ∈ h.horizontal_logderiv_control.carrier.carrier :=
    h.horizontal_logderiv_control.top_mem u x hx
  let hraw :
      ‖completedZetaNegLogDeriv z‖ ≤
        h.horizontal_logderiv_control.bound_constant *
          (1 + ‖z.im‖) ^
            h.horizontal_logderiv_control.growth_degree :=
    h.horizontal_logderiv_control.bound z hz
  let him :
      ‖z.im‖ = ‖h.height_schedule.height u‖ :=
    zetaCompletedExplicitFormulaTopPath_im_norm
      (F.rectangle (h.height_schedule.height u)) x
  let htarget :
      h.horizontal_logderiv_control.bound_constant *
          (1 + ‖z.im‖) ^
            h.horizontal_logderiv_control.growth_degree =
        h.horizontal_logderiv_control.bound_constant *
          (1 + ‖h.height_schedule.height u‖) ^
            h.horizontal_logderiv_control.growth_degree :=
    congrArg
      (fun value : ℝ =>
        h.horizontal_logderiv_control.bound_constant *
          (1 + value) ^ h.horizontal_logderiv_control.growth_degree)
      him
  hraw.trans_eq htarget

/-- The bottom horizontal path bound stored in a polynomial scheduled package. -/
theorem ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage.bottomPath_completedZetaNegLogDeriv_bound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ‖completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x)‖ ≤
      h.horizontal_logderiv_control.bound_constant *
        (1 + ‖h.height_schedule.height u‖) ^
          h.horizontal_logderiv_control.growth_degree :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x
  let hz : z ∈ h.horizontal_logderiv_control.carrier.carrier :=
    h.horizontal_logderiv_control.bottom_mem u x hx
  let hraw :
      ‖completedZetaNegLogDeriv z‖ ≤
        h.horizontal_logderiv_control.bound_constant *
          (1 + ‖z.im‖) ^
            h.horizontal_logderiv_control.growth_degree :=
    h.horizontal_logderiv_control.bound z hz
  let him :
      ‖z.im‖ = ‖h.height_schedule.height u‖ :=
    zetaCompletedExplicitFormulaBottomPath_im_norm
      (F.rectangle (h.height_schedule.height u)) x
  let htarget :
      h.horizontal_logderiv_control.bound_constant *
          (1 + ‖z.im‖) ^
            h.horizontal_logderiv_control.growth_degree =
        h.horizontal_logderiv_control.bound_constant *
          (1 + ‖h.height_schedule.height u‖) ^
            h.horizontal_logderiv_control.growth_degree :=
    congrArg
      (fun value : ℝ =>
        h.horizontal_logderiv_control.bound_constant *
          (1 + value) ^ h.horizontal_logderiv_control.growth_degree)
      him
  hraw.trans_eq htarget

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
