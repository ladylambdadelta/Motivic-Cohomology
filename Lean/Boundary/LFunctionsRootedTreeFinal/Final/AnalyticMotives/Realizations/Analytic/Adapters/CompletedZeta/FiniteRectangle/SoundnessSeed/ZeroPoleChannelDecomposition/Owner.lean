import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.Channels.Owner

/-!
# Zero-pole scheduled channel decomposition

This file exposes the scheduled zero-pole rectangle bookkeeping identity as a
concrete analytic trace-value equality.

The imported RH-lane theorem says that the late left vertical trace equals the
right vertical trace plus the horizontal remainder minus the rectangle boundary
trace.  In the trace computad this is a channel-decomposition seed: one
scheduled contour expression is decomposed into visible right, horizontal, and
boundary channels.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left vertical zero-pole trace in the scheduled rectangle family. -/
noncomputable def completedZetaZeroPoleLeftVerticalTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
    f F (h.height_schedule.height u)

/-- The right vertical zero-pole trace in the scheduled rectangle family. -/
noncomputable def completedZetaZeroPoleRightVerticalTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
    f F (h.height_schedule.height u)

/-- The scheduled horizontal zero-pole remainder trace. -/
noncomputable def completedZetaZeroPoleHorizontalTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
    f F h u

/-- The scheduled zero-pole rectangle-boundary trace. -/
noncomputable def completedZetaZeroPoleRectangleBoundaryTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
    f F (h.height_schedule.height u)

/--
The imported scheduled rectangle algebra identity, expressed as a channel
decomposition of concrete analytic trace values.
-/
theorem completedZetaZeroPoleLeftVerticalTrace_eq_channels
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_horizontal_sub_boundary
    f F h u

/-- The zero-pole channel target is the generic analytic channel decomposition. -/
theorem completedZetaZeroPoleChannelTarget_eq_analyticChannelDecomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    AnalyticTraceValue.channelDecomposition
        (completedZetaZeroPoleRightVerticalTrace f F h u)
        (completedZetaZeroPoleHorizontalTrace f F h u)
        (completedZetaZeroPoleRectangleBoundaryTrace f F h u) =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  AnalyticTraceValue.channelDecomposition_eq
    (completedZetaZeroPoleRightVerticalTrace f F h u)
    (completedZetaZeroPoleHorizontalTrace f F h u)
    (completedZetaZeroPoleRectangleBoundaryTrace f F h u)

end AnalyticMotives
end LFunctions
end Boundary
