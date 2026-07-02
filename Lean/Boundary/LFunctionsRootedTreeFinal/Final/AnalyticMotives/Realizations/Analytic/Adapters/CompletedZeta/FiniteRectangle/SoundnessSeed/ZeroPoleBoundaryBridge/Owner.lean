import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleBoundaryRefinement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectanglePipeline.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectanglePipeline.Owner

/-!
# Zero-pole boundary bridge at the scheduled channel rectangle

This file records the concrete analytic bridge currently available between the
scheduled channel rectangle and the finite-square residue rectangle.

The bridge is trace-value level.  It evaluates the already-proved standard and
tangent boundary refinements at the scheduled channel pipeline rectangle height,
and evaluates the residue rectangle pipeline at that same height.  It stops at
the theorem currently supplied by the analytic owner chain: the channel
theorem's rectangle-boundary trace is not identified here with the standard or
tangent boundary traces.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The scheduled channel pipeline rectangle height. -/
def completedZetaZeroPoleChannelPipelineRectangleHeight
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ℝ :=
  (completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangle
    f F h u).T

/-- The scheduled channel pipeline height is the height schedule value. -/
theorem completedZetaZeroPoleChannelPipelineRectangleHeight_eq_schedule
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelPipelineRectangleHeight f F h u =
      h.height_schedule.height u :=
  rfl

/-- The standard boundary trace evaluated at the scheduled channel pipeline rectangle height. -/
noncomputable def completedZetaZeroPoleChannelPipelineStandardBoundaryTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ℂ :=
  completedZetaZeroPoleStandardBoundaryTrace
    f F
    (completedZetaZeroPoleChannelPipelineRectangleHeight f F h u)

/-- The tangent boundary trace evaluated at the scheduled channel pipeline rectangle height. -/
noncomputable def completedZetaZeroPoleChannelPipelineTangentBoundaryTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ℂ :=
  completedZetaZeroPoleTangentBoundaryTrace
    f F
    (completedZetaZeroPoleChannelPipelineRectangleHeight f F h u)

/-- The orientation defect evaluated at the scheduled channel pipeline rectangle height. -/
noncomputable def completedZetaZeroPoleChannelPipelineOrientationDefectTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ℂ :=
  completedZetaZeroPoleTangentOrientationDefectTrace
    f F
    (completedZetaZeroPoleChannelPipelineRectangleHeight f F h u)

/-- The pipeline standard boundary trace is the scheduled standard boundary trace. -/
theorem completedZetaZeroPoleChannelPipelineStandardBoundaryTrace_eq_scheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelPipelineStandardBoundaryTrace f F h u =
      completedZetaZeroPoleScheduledStandardBoundaryTrace f F h u :=
  rfl

/-- The pipeline tangent boundary trace is the scheduled tangent boundary trace. -/
theorem completedZetaZeroPoleChannelPipelineTangentBoundaryTrace_eq_scheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelPipelineTangentBoundaryTrace f F h u =
      completedZetaZeroPoleScheduledTangentBoundaryTrace f F h u :=
  rfl

/-- The pipeline orientation defect is the scheduled orientation defect. -/
theorem completedZetaZeroPoleChannelPipelineOrientationDefectTrace_eq_scheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelPipelineOrientationDefectTrace f F h u =
      completedZetaZeroPoleScheduledTangentOrientationDefectTrace f F h u :=
  rfl

/-- The standard boundary at the pipeline rectangle height is the finite-square residue trace. -/
theorem completedZetaZeroPoleChannelPipelineStandardBoundaryTrace_eq_finiteSquareResidueTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 0 < completedZetaZeroPoleChannelPipelineRectangleHeight f F h u) :
    completedZetaZeroPoleChannelPipelineStandardBoundaryTrace f F h u =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleScheduledStandardBoundaryTrace_eq_finiteSquareResidueTrace
    f F h u hT

/--
The tangent boundary at the pipeline rectangle height is the finite-square
residue trace plus the orientation defect.
-/
theorem completedZetaZeroPoleChannelPipelineTangentBoundaryTrace_eq_finiteSquareResidueTrace_add_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 0 < completedZetaZeroPoleChannelPipelineRectangleHeight f F h u) :
    completedZetaZeroPoleChannelPipelineTangentBoundaryTrace f F h u =
      completedZetaZeroPoleFiniteSquareResidueTrace f +
        completedZetaZeroPoleChannelPipelineOrientationDefectTrace f F h u :=
  completedZetaZeroPoleScheduledTangentBoundaryTrace_eq_finiteSquareResidueTrace_add_orientationDefect
    f F h u hT

/--
The residue rectangle pipeline is sound when its height is chosen to be the
scheduled channel pipeline rectangle height.
-/
theorem completedZetaZeroPoleResidueRectanglePipeline_sound_at_channelPipelineHeight
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 0 < completedZetaZeroPoleChannelPipelineRectangleHeight f F h u) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace
      f
      (completedZetaZeroPoleChannelPipelineRectangleHeight f F h u) =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectanglePipeline_sound_of_rectangleHeight
    f h.phi_control hT

/--
At the scheduled channel pipeline height, both the standard boundary refinement
and the residue rectangle pipeline land on the same finite-square residue trace.
-/
theorem completedZetaZeroPoleChannelPipelineStandardBoundaryTrace_eq_residueRectanglePipelineTarget
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 0 < completedZetaZeroPoleChannelPipelineRectangleHeight f F h u) :
    completedZetaZeroPoleChannelPipelineStandardBoundaryTrace f F h u =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleChannelPipelineStandardBoundaryTrace_eq_finiteSquareResidueTrace
    f F h u hT

end AnalyticMotives
end LFunctions
end Boundary
