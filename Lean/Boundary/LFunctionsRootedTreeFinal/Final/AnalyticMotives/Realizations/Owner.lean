import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Comparison.Summary.Owner

/-!
# Realizations of the trace computad

This directory owns the two current interpretations of the synthetic trace
computad:

* analytic realization by contour, residue, channel, refinement, schedule,
  weight drop, and Fubini calculus;
* algebraic-facing realization by Q-linear trace correspondences and the
  representable/Yoneda calculus, with finite-correspondence comparison supplied
  downstream.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The current analytic and algebraic realizations agree on Stokes generators. -/
theorem TraceRealizations.stokesMap_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceAlgebraicRealizationGenerator.stokesMap source target :=
  TraceRealizationComparison.currentStokesMapAgreement
    source
    target

/-- The current analytic and algebraic realizations agree on residue generators. -/
theorem TraceRealizations.residueMap_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceAlgebraicRealizationGenerator.residueMap source target :=
  TraceRealizationComparison.currentResidueMapAgreement
    source
    target

/-- The current analytic and algebraic realizations agree on channel generators. -/
theorem TraceRealizations.channelMap_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceAlgebraicRealizationGenerator.channelMap source target :=
  TraceRealizationComparison.currentChannelMapAgreement
    source
    target

/-- The current analytic and algebraic realizations agree on refinement generators. -/
theorem TraceRealizations.refinementMap_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceAlgebraicRealizationGenerator.refinementMap source target :=
  TraceRealizationComparison.currentRefinementMapAgreement
    source
    target

/-- The current analytic and algebraic realizations agree on schedule generators. -/
theorem TraceRealizations.scheduleMap_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceAlgebraicRealizationGenerator.scheduleMap source target :=
  TraceRealizationComparison.currentScheduleMapAgreement
    source
    target

/-- The current analytic and algebraic realizations agree on weight-drop generators. -/
theorem TraceRealizations.weightDropMap_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceAlgebraicRealizationGenerator.weightDropMap source target :=
  TraceRealizationComparison.currentWeightDropMapAgreement
    source
    target

/-- The current analytic and algebraic realizations agree on Fubini generators. -/
theorem TraceRealizations.fubiniMap_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceAlgebraicRealizationGenerator.fubiniMap source target :=
  TraceRealizationComparison.currentFubiniMapAgreement
    source
    target

/-- The common Stokes realization has the Stokes trace hom as preimage. -/
theorem TraceRealizations.analyticStokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticRealization.stokesMap_preimage
    source
    target

/-- The common residue realization has the residue trace hom as preimage. -/
theorem TraceRealizations.analyticResidueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticRealization.residueMap_preimage
    source
    target

/-- The common channel realization has the channel trace hom as preimage. -/
theorem TraceRealizations.analyticChannelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticRealization.channelMap_preimage
    source
    target

/-- The common refinement realization has the refinement trace hom as preimage. -/
theorem TraceRealizations.analyticRefinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticRealization.refinementMap_preimage
    source
    target

/-- The common schedule realization has the schedule trace hom as preimage. -/
theorem TraceRealizations.analyticScheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticRealization.scheduleMap_preimage
    source
    target

/-- The common weight-drop realization has the weight-drop trace hom as preimage. -/
theorem TraceRealizations.analyticWeightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticRealization.weightDropMap_preimage
    source
    target

/-- The common Fubini realization has the Fubini trace hom as preimage. -/
theorem TraceRealizations.analyticFubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticRealization.fubiniMap_preimage
    source
    target

/-- The algebraic Stokes realization has the same Stokes trace hom as preimage. -/
theorem TraceRealizations.algebraicStokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAlgebraicRealization.stokesMap_preimage
    source
    target

/-- The algebraic residue realization has the same residue trace hom as preimage. -/
theorem TraceRealizations.algebraicResidueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAlgebraicRealization.residueMap_preimage
    source
    target

/-- The algebraic channel realization has the same channel trace hom as preimage. -/
theorem TraceRealizations.algebraicChannelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAlgebraicRealization.channelMap_preimage
    source
    target

/-- The algebraic refinement realization has the same refinement trace hom as preimage. -/
theorem TraceRealizations.algebraicRefinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAlgebraicRealization.refinementMap_preimage
    source
    target

/-- The algebraic schedule realization has the same schedule trace hom as preimage. -/
theorem TraceRealizations.algebraicScheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAlgebraicRealization.scheduleMap_preimage
    source
    target

/-- The algebraic weight-drop realization has the same weight-drop trace hom as preimage. -/
theorem TraceRealizations.algebraicWeightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAlgebraicRealization.weightDropMap_preimage
    source
    target

/-- The algebraic Fubini realization has the same Fubini trace hom as preimage. -/
theorem TraceRealizations.algebraicFubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAlgebraicRealization.fubiniMap_preimage
    source
    target

/-- The realization root exposes completed-zeta zero-pole residue soundness. -/
theorem TraceRealizations.completedZeta_zeroPole_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  TraceAnalyticRealization.completedZeta_zeroPole_residueGenerator_sound
    f
    hPhi
    hR

/-- The realization root exposes completed-zeta zero-pole channel soundness. -/
theorem TraceRealizations.completedZeta_zeroPole_channelGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  TraceAnalyticRealization.completedZeta_zeroPole_channelGenerator_sound
    f
    F
    h
    u

/-- The realization root exposes the first completed-zeta quotient relation. -/
theorem TraceRealizations.completedZeta_zeroPole_quotientClass_eq_empty :
    TraceCorQQuotient.ofCandidate
        completedZetaZeroPoleTraceCorQQuotientCandidate =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  TraceAnalyticRealization.completedZeta_zeroPole_quotientClass_eq_empty

end AnalyticMotives
end LFunctions
end Boundary
