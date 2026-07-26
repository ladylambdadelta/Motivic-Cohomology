import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner

/-!
# Scheduled horizontal log-derivative control

This file owns the narrow log-derivative control actually consumed by horizontal
decay: one scheduled horizontal carrier, its top and bottom membership maps, and
concrete polynomial constants on that carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Log-derivative control on the scheduled horizontal carrier of a contour family. -/
structure ExplicitFormulaScheduledHorizontalLogDerivControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (heightSchedule : ExplicitFormulaCofinalHeightSchedule F) where
  /-- The shared zero-excised carrier containing all scheduled horizontal points. -/
  carrier :
    CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c))
  /-- The scheduled top edge lands in the shared carrier. -/
  top_mem :
    ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      zetaCompletedExplicitFormulaTopPath
        (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier
  /-- The scheduled bottom edge lands in the shared carrier. -/
  bottom_mem :
    ∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (heightSchedule.height u)) x ∈ carrier.carrier
  /-- A concrete polynomial-growth constant on the scheduled carrier. -/
  bound_constant : ℕ → ℝ
  /-- The scheduled-carrier bound constants are positive. -/
  bound_constant_pos : ∀ N : ℕ, 0 < bound_constant N
  /-- The concrete constants bound the completed negative logarithmic derivative. -/
  bound :
    ∀ (N : ℕ) (z : ℂ),
      z ∈ carrier.carrier →
        ‖completedZetaNegLogDeriv z‖ ≤
          bound_constant N * (1 + ‖z.im‖) ^ N

/-- Scheduled analytic package with only the log-derivative control needed on the
scheduled horizontal carrier. -/
structure ExplicitFormulaScheduledFamilyAnalyticPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) where
  /-- Transform decay and regularity for the probe. -/
  phi_control : ZetaPhiAnalyticControl f
  /-- The cofinal height schedule for the contour family. -/
  height_schedule : ExplicitFormulaCofinalHeightSchedule F
  /-- Concrete completed-log-derivative bounds on the scheduled horizontal carrier. -/
  horizontal_logderiv_control :
    ExplicitFormulaScheduledHorizontalLogDerivControl f F height_schedule

/-- The scheduled package stores the same height schedule as its projection. -/
theorem ExplicitFormulaScheduledFamilyAnalyticPackage.height_schedule_eq
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) :
    h.height_schedule = h.height_schedule :=
  rfl

/-- The scheduled package stores the same transform control as its projection. -/
theorem ExplicitFormulaScheduledFamilyAnalyticPackage.phi_control_eq
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) :
    h.phi_control = h.phi_control :=
  rfl

/-- A full family analytic package induces scheduled horizontal log-derivative control. -/
def ExplicitFormulaFamilyAnalyticPackage.toScheduledHorizontalLogDerivControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaScheduledHorizontalLogDerivControl f F h.height_schedule :=
  let scheduled := h.scheduled_horizontalFamilyZeroExcisedStrip
  Exists.elim scheduled
    (fun carrier hmem =>
      { carrier := carrier
        top_mem := hmem.1
        bottom_mem := hmem.2
        bound_constant :=
          fun N : ℕ =>
            h.logderiv_control.zeroExcisedStripBoundConstant
              (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier N
        bound_constant_pos :=
          fun N : ℕ =>
            h.logderiv_control.zeroExcisedStripBoundConstant_pos
              (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier N
        bound :=
          fun N z hz =>
            h.logderiv_control.zeroExcisedStripBoundConstant_bound
              (min F.c (1 - F.c)) (max F.c (1 - F.c)) carrier N z hz })

/-- A full family analytic package forgets to the scheduled-horizontal package. -/
def ExplicitFormulaFamilyAnalyticPackage.toScheduledFamilyAnalyticPackage
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaScheduledFamilyAnalyticPackage f F :=
  { phi_control := h.phi_control
    height_schedule := h.height_schedule
    horizontal_logderiv_control :=
      h.toScheduledHorizontalLogDerivControl }

/-- The scheduled-control carrier is exactly the stored carrier projection. -/
theorem ExplicitFormulaScheduledHorizontalLogDerivControl.carrier_eq
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (h : ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule) :
    h.carrier = h.carrier :=
  rfl

/-- The scheduled-control bound constant is positive. -/
theorem ExplicitFormulaScheduledHorizontalLogDerivControl.boundConstant_pos
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (h : ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (N : ℕ) :
    0 < h.bound_constant N :=
  h.bound_constant_pos N

/-- The scheduled-control bound controls the completed negative logarithmic derivative. -/
theorem ExplicitFormulaScheduledHorizontalLogDerivControl.bound_of_mem
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    {heightSchedule : ExplicitFormulaCofinalHeightSchedule F}
    (h : ExplicitFormulaScheduledHorizontalLogDerivControl f F heightSchedule)
    (N : ℕ) (z : ℂ) (hz : z ∈ h.carrier.carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤
      h.bound_constant N * (1 + ‖z.im‖) ^ N :=
  h.bound N z hz

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
