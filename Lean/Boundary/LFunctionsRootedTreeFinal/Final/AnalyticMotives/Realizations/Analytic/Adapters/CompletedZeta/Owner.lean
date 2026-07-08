import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.Owner

/-!
# Completed-zeta analytic adapters

This directory owns completed-zeta analytic realization adapters for the trace
computad.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The completed-zeta adapter exposes the finite-square zero-pole residue equality. -/
theorem completedZetaAdapter.zeroPole_boundaryTrace_eq_residueTrace
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaFiniteRectangle.zeroPole_boundaryTrace_eq_residueTrace
    f
    hPhi
    hR

/-- The completed-zeta adapter exposes zero-pole residue-generator soundness. -/
theorem completedZetaAdapter.zeroPole_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaFiniteRectangle.zeroPole_residueGenerator_sound
    f
    hPhi
    hR

/-- The completed-zeta adapter exposes zero-pole channel-generator soundness. -/
theorem completedZetaAdapter.zeroPole_channelGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaFiniteRectangle.zeroPole_channelGenerator_sound
    f
    F
    h
    u

/-- The completed-zeta adapter exposes the rectangle-certified residue pipeline. -/
theorem completedZetaAdapter.zeroPole_residueRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaFiniteRectangle.zeroPole_residueRectanglePipeline_sound
    f
    hPhi
    hR

/-- The completed-zeta adapter exposes the scheduled channel rectangle pipeline. -/
theorem completedZetaAdapter.zeroPole_channelRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaFiniteRectangle.zeroPole_channelRectanglePipeline_sound
    f
    F
    h
    u

/-- The completed-zeta adapter exposes the first quotient relation from the analytic chain. -/
theorem completedZetaAdapter.zeroPole_quotientClass_eq_empty :
    TraceCorQQuotient.ofCandidate
        completedZetaZeroPoleTraceCorQQuotientCandidate =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  completedZetaFiniteRectangle.zeroPole_quotientClass_eq_empty

end AnalyticMotives
end LFunctions
end Boundary
