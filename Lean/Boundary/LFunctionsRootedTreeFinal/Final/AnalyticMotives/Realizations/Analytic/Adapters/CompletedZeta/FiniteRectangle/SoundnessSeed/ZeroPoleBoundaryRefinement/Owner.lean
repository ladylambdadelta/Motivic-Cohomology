import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelDecomposition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleTraceValue.Owner

/-!
# Zero-pole boundary refinement

This file exposes the positive-height Cauchy refinement that identifies the
outer standard zero-pole boundary with the raw `2*pi*i` residue value.

This is the analytic bridge needed before composing the channel-decomposition
transport with residue extraction: the boundary channel must first be related
to the standard zero-pole contour boundary theorem supplied by the RH lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The outer standard zero-pole boundary trace at a finite rectangle height. -/
noncomputable def completedZetaZeroPoleStandardBoundaryTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
    f F T

/-- The outer standard zero-pole boundary trace on a scheduled rectangle. -/
noncomputable def completedZetaZeroPoleScheduledStandardBoundaryTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  completedZetaZeroPoleStandardBoundaryTrace
    f F (h.height_schedule.height u)

/-- The tangent-oriented zero-pole boundary trace at a finite rectangle height. -/
noncomputable def completedZetaZeroPoleTangentBoundaryTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
    f F T

/-- The tangent-oriented zero-pole boundary trace on a scheduled rectangle. -/
noncomputable def completedZetaZeroPoleScheduledTangentBoundaryTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  completedZetaZeroPoleTangentBoundaryTrace
    f F (h.height_schedule.height u)

/-- The tangent-to-standard orientation defect at a finite rectangle height. -/
noncomputable def completedZetaZeroPoleTangentOrientationDefectTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
    f F T

/-- The tangent-to-standard orientation defect on a scheduled rectangle. -/
noncomputable def completedZetaZeroPoleScheduledTangentOrientationDefectTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  completedZetaZeroPoleTangentOrientationDefectTrace
    f F (h.height_schedule.height u)

/-- The raw `2*pi*i` normalized zero-pole residue value. -/
noncomputable def completedZetaZeroPoleRawResidueTrace
    (f : ZetaAdmissibleFunction) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) *
    (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))

/-- The raw residue trace agrees definitionally with the finite-square residue trace. -/
theorem completedZetaZeroPoleRawResidueTrace_eq_finiteSquareResidueTrace
    (f : ZetaAdmissibleFunction) :
    completedZetaZeroPoleRawResidueTrace f =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  rfl

/--
The positive-height outer-boundary Cauchy refinement for the zero-pole
correction kernel.
-/
theorem completedZetaZeroPoleStandardBoundaryTrace_eq_rawResidueTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) {T : ℝ} (hT : 0 < T) :
    completedZetaZeroPoleStandardBoundaryTrace f F T =
      completedZetaZeroPoleRawResidueTrace f :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
    f F hPhi hT

/--
The positive-height outer-boundary Cauchy refinement, expressed with the
finite-square residue trace value used by the residue seed.
-/
theorem completedZetaZeroPoleStandardBoundaryTrace_eq_finiteSquareResidueTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) {T : ℝ} (hT : 0 < T) :
    completedZetaZeroPoleStandardBoundaryTrace f F T =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  Eq.trans
    (completedZetaZeroPoleStandardBoundaryTrace_eq_rawResidueTrace
      f F hPhi hT)
    (completedZetaZeroPoleRawResidueTrace_eq_finiteSquareResidueTrace f)

/--
The scheduled outer-boundary Cauchy refinement for the zero-pole correction
kernel.
-/
theorem completedZetaZeroPoleScheduledStandardBoundaryTrace_eq_rawResidueTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 0 < h.height_schedule.height u) :
    completedZetaZeroPoleScheduledStandardBoundaryTrace f F h u =
      completedZetaZeroPoleRawResidueTrace f :=
  completedZetaZeroPoleStandardBoundaryTrace_eq_rawResidueTrace
    f F h.phi_control hT

/--
The scheduled outer-boundary Cauchy refinement, expressed with the
finite-square residue trace value used by the residue seed.
-/
theorem completedZetaZeroPoleScheduledStandardBoundaryTrace_eq_finiteSquareResidueTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 0 < h.height_schedule.height u) :
    completedZetaZeroPoleScheduledStandardBoundaryTrace f F h u =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  Eq.trans
    (completedZetaZeroPoleScheduledStandardBoundaryTrace_eq_rawResidueTrace
      f F h u hT)
    (completedZetaZeroPoleRawResidueTrace_eq_finiteSquareResidueTrace f)

/--
The tangent-oriented zero-pole boundary is the standard boundary plus the
orientation defect.
-/
theorem completedZetaZeroPoleTangentBoundaryTrace_eq_standard_add_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    completedZetaZeroPoleTangentBoundaryTrace f F T =
      completedZetaZeroPoleStandardBoundaryTrace f F T +
        completedZetaZeroPoleTangentOrientationDefectTrace f F T :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_standard_add_orientationDefect
    f F T

/--
Scheduled tangent-to-standard orientation decomposition for the zero-pole
boundary trace.
-/
theorem completedZetaZeroPoleScheduledTangentBoundaryTrace_eq_standard_add_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleScheduledTangentBoundaryTrace f F h u =
      completedZetaZeroPoleScheduledStandardBoundaryTrace f F h u +
        completedZetaZeroPoleScheduledTangentOrientationDefectTrace f F h u :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentBoundary_eq_standard_add_orientationDefect
    f F h u

/--
The scheduled tangent orientation defect is two copies of the scheduled
horizontal zero-pole remainder.
-/
theorem completedZetaZeroPoleScheduledTangentOrientationDefectTrace_eq_horizontal_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleScheduledTangentOrientationDefectTrace f F h u =
      completedZetaZeroPoleHorizontalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledOrientationDefect_eq_horizontal_add_horizontal
    f F h u

/--
The scheduled tangent-oriented boundary is the finite-square residue trace plus
the scheduled orientation defect, at positive scheduled height.
-/
theorem completedZetaZeroPoleScheduledTangentBoundaryTrace_eq_finiteSquareResidueTrace_add_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 0 < h.height_schedule.height u) :
    completedZetaZeroPoleScheduledTangentBoundaryTrace f F h u =
      completedZetaZeroPoleFiniteSquareResidueTrace f +
        completedZetaZeroPoleScheduledTangentOrientationDefectTrace f F h u :=
  Eq.trans
    (completedZetaZeroPoleScheduledTangentBoundaryTrace_eq_standard_add_orientationDefect
      f F h u)
    (congrArg
      (fun z : ℂ =>
        z + completedZetaZeroPoleScheduledTangentOrientationDefectTrace f F h u)
      (completedZetaZeroPoleScheduledStandardBoundaryTrace_eq_finiteSquareResidueTrace
        f F h u hT))

end AnalyticMotives
end LFunctions
end Boundary
