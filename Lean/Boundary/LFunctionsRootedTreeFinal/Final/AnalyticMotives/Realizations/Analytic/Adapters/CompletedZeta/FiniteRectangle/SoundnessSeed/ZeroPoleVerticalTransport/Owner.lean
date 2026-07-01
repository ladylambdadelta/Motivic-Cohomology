import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleBoundaryRefinement.Owner

/-!
# Zero-pole vertical-orientation transport

This file exposes the concrete RH-lane transport from tangent-oriented
boundary residue data to the ordinary right vertical channel.

The point is not a pointwise equality between the non-tangent rectangle
boundary and the tangent/standard boundary.  The vertical sides differ by the
missing tangent factor `I`.  The existing RH-lane theorem handles the correct
analytic transport at the scheduled-limit level.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The scheduled right vertical zero-pole trace as a function of the schedule parameter. -/
noncomputable def completedZetaZeroPoleScheduledRightVerticalTraceFunction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) : ℝ → ℂ :=
  fun u : ℝ => completedZetaZeroPoleRightVerticalTrace f F h u

/-- The scheduled left vertical zero-pole trace as a function of the schedule parameter. -/
noncomputable def completedZetaZeroPoleScheduledLeftVerticalTraceFunction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) : ℝ → ℂ :=
  fun u : ℝ => completedZetaZeroPoleLeftVerticalTrace f F h u

/-- The scheduled horizontal zero-pole trace as a function of the schedule parameter. -/
noncomputable def completedZetaZeroPoleScheduledHorizontalTraceFunction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) : ℝ → ℂ :=
  fun u : ℝ => completedZetaZeroPoleHorizontalTrace f F h u

/-- The scheduled tangent-boundary zero-pole trace as a function of the schedule parameter. -/
noncomputable def completedZetaZeroPoleScheduledTangentBoundaryTraceFunction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) : ℝ → ℂ :=
  fun u : ℝ => completedZetaZeroPoleScheduledTangentBoundaryTrace f F h u

/--
Vertical-orientation transport from tangent-boundary residue convergence to
the right vertical channel.

This is the analytic bridge that replaces any false pointwise identification
between the non-tangent rectangle boundary and the tangent/standard boundary.
-/
theorem completedZetaZeroPoleRightVerticalTrace_tendsto_of_tangentBoundaryTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (B : ℂ)
    (hleft :
      Tendsto
        (completedZetaZeroPoleScheduledLeftVerticalTraceFunction f F h)
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (completedZetaZeroPoleScheduledHorizontalTraceFunction f F h)
        atTop
        (𝓝 0))
    (htangent :
      Tendsto
        (completedZetaZeroPoleScheduledTangentBoundaryTraceFunction f F h)
        atTop
        (𝓝 B)) :
    Tendsto
      (completedZetaZeroPoleScheduledRightVerticalTraceFunction f F h)
      atTop
      (𝓝 (-(B * Complex.I))) :=
  zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_tangentBoundaryResidue_ownerAssembly
    f F h B hleft hhorizontal htangent

/--
Vertical-orientation transport specialized to the finite-square residue trace
plus a tangent orientation defect limit.
-/
theorem completedZetaZeroPoleRightVerticalTrace_tendsto_of_finiteSquareResidueTrace_and_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (D : ℂ)
    (hleft :
      Tendsto
        (completedZetaZeroPoleScheduledLeftVerticalTraceFunction f F h)
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (completedZetaZeroPoleScheduledHorizontalTraceFunction f F h)
        atTop
        (𝓝 0))
    (htangent :
      Tendsto
        (completedZetaZeroPoleScheduledTangentBoundaryTraceFunction f F h)
        atTop
        (𝓝 (completedZetaZeroPoleFiniteSquareResidueTrace f + D))) :
    Tendsto
      (completedZetaZeroPoleScheduledRightVerticalTraceFunction f F h)
      atTop
      (𝓝 (-((completedZetaZeroPoleFiniteSquareResidueTrace f + D) * Complex.I))) :=
  completedZetaZeroPoleRightVerticalTrace_tendsto_of_tangentBoundaryTrace
    f F h
    (completedZetaZeroPoleFiniteSquareResidueTrace f + D)
    hleft
    hhorizontal
    htangent

end AnalyticMotives
end LFunctions
end Boundary
