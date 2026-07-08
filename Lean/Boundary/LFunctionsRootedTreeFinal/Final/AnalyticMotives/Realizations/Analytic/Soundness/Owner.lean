import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Soundness.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Soundness.Paths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Soundness.Coherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.Owner

/-!
# Analytic soundness

This directory owns the proof that the analytic realization faithfully
interprets the synthetic trace computad.

The general soundness subowners remain independent of any single L-function.
This root file may expose concrete proved adapter instances of soundness.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Analytic soundness exposes the completed-zeta finite-square residue equality. -/
theorem TraceAnalyticSoundness.completedZeta_zeroPole_boundaryTrace_eq_residueTrace
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  analyticAdapter.completedZeta_zeroPole_boundaryTrace_eq_residueTrace
    f
    hPhi
    hR

/-- Analytic soundness exposes the completed-zeta zero-pole residue generator. -/
theorem TraceAnalyticSoundness.completedZeta_zeroPole_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  analyticAdapter.completedZeta_zeroPole_residueGenerator_sound
    f
    hPhi
    hR

/-- Analytic soundness exposes the completed-zeta zero-pole channel generator. -/
theorem TraceAnalyticSoundness.completedZeta_zeroPole_channelGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  analyticAdapter.completedZeta_zeroPole_channelGenerator_sound
    f
    F
    h
    u

/-- Analytic soundness exposes the completed-zeta rectangle-certified residue pipeline. -/
theorem TraceAnalyticSoundness.completedZeta_zeroPole_residueRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  analyticAdapter.completedZeta_zeroPole_residueRectanglePipeline_sound
    f
    hPhi
    hR

/-- Analytic soundness exposes the completed-zeta scheduled channel rectangle pipeline. -/
theorem TraceAnalyticSoundness.completedZeta_zeroPole_channelRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  analyticAdapter.completedZeta_zeroPole_channelRectanglePipeline_sound
    f
    F
    h
    u

/-- Analytic soundness exposes the first completed-zeta quotient relation. -/
theorem TraceAnalyticSoundness.completedZeta_zeroPole_quotientClass_eq_empty :
    TraceCorQQuotient.ofCandidate
        completedZetaZeroPoleTraceCorQQuotientCandidate =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  analyticAdapter.completedZeta_zeroPole_quotientClass_eq_empty

end AnalyticMotives
end LFunctions
end Boundary
