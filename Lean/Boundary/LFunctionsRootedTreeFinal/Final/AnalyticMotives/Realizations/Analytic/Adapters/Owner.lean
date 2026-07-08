import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.Owner

/-!
# Analytic realization adapters

This directory owns adapters from concrete analytic owner theorem families in
`Final` into the analytic realization of the trace computad.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Analytic adapters expose the completed-zeta finite-square zero-pole residue equality. -/
theorem analyticAdapter.completedZeta_zeroPole_boundaryTrace_eq_residueTrace
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaAdapter.zeroPole_boundaryTrace_eq_residueTrace
    f
    hPhi
    hR

/-- Analytic adapters expose completed-zeta zero-pole residue-generator soundness. -/
theorem analyticAdapter.completedZeta_zeroPole_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaAdapter.zeroPole_residueGenerator_sound
    f
    hPhi
    hR

/-- Analytic adapters expose completed-zeta zero-pole channel-generator soundness. -/
theorem analyticAdapter.completedZeta_zeroPole_channelGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaAdapter.zeroPole_channelGenerator_sound
    f
    F
    h
    u

/-- Analytic adapters expose the completed-zeta rectangle-certified residue pipeline. -/
theorem analyticAdapter.completedZeta_zeroPole_residueRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaAdapter.zeroPole_residueRectanglePipeline_sound
    f
    hPhi
    hR

/-- Analytic adapters expose the completed-zeta scheduled channel rectangle pipeline. -/
theorem analyticAdapter.completedZeta_zeroPole_channelRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaAdapter.zeroPole_channelRectanglePipeline_sound
    f
    F
    h
    u

/-- Analytic adapters expose the first completed-zeta quotient relation. -/
theorem analyticAdapter.completedZeta_zeroPole_quotientClass_eq_empty :
    TraceCorQQuotient.ofCandidate
        completedZetaZeroPoleTraceCorQQuotientCandidate =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  completedZetaAdapter.zeroPole_quotientClass_eq_empty

end AnalyticMotives
end LFunctions
end Boundary
