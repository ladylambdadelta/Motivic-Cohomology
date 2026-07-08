import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.TraceValue.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Soundness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.Owner

/-!
# Analytic realization

This directory owns the realization of the trace computad by concrete analytic
contour calculus.

Adapters here may import the RH lane and other `Final` analytic owner files
heavily.  They must not edit those lanes or make the zeta presentation define
the general computad.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic realization root exposes boundary trace values as complex values. -/
theorem TraceAnalyticRealization.boundaryTraceValue_eq
    (value : ℂ) :
    AnalyticTraceValue.boundary value =
      value :=
  AnalyticTraceValue.boundary_eq
    value

/-- The analytic realization root exposes residue trace values as complex values. -/
theorem TraceAnalyticRealization.residueTraceValue_eq
    (value : ℂ) :
    AnalyticTraceValue.residue value =
      value :=
  AnalyticTraceValue.residue_eq
    value

/-- The analytic realization root exposes channel-decomposition trace values. -/
theorem TraceAnalyticRealization.channelDecompositionTraceValue_eq
    (right horizontal boundary : AnalyticTraceValue) :
    AnalyticTraceValue.channelDecomposition
        right
        horizontal
        boundary =
      right + horizontal - boundary :=
  AnalyticTraceValue.channelDecomposition_eq
    right
    horizontal
    boundary

/-- The analytic Stokes-realization map is the Stokes by-kind representable map. -/
theorem TraceAnalyticRealization.stokesMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.stokesMap_eq
    source
    target

/-- The analytic residue-realization map is the residue by-kind representable map. -/
theorem TraceAnalyticRealization.residueMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.residueMap_eq
    source
    target

/-- The analytic channel-realization map is the channel by-kind representable map. -/
theorem TraceAnalyticRealization.channelMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.channelMap_eq
    source
    target

/-- The analytic refinement-realization map is the refinement by-kind representable map. -/
theorem TraceAnalyticRealization.refinementMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.refinementMap_eq
    source
    target

/-- The analytic schedule-realization map is the schedule by-kind representable map. -/
theorem TraceAnalyticRealization.scheduleMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.scheduleMap_eq
    source
    target

/-- The analytic weight-drop-realization map is the weight-drop by-kind representable map. -/
theorem TraceAnalyticRealization.weightDropMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.weightDropMap_eq
    source
    target

/-- The analytic Fubini-realization map is the Fubini by-kind representable map. -/
theorem TraceAnalyticRealization.fubiniMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.fubiniMap_eq
    source
    target

/-- The analytic Stokes-realization map has the Stokes trace hom as preimage. -/
theorem TraceAnalyticRealization.stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticRealizationGenerator.stokesMap_preimage
    source
    target

/-- The analytic residue-realization map has the residue trace hom as preimage. -/
theorem TraceAnalyticRealization.residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticRealizationGenerator.residueMap_preimage
    source
    target

/-- The analytic channel-realization map has the channel trace hom as preimage. -/
theorem TraceAnalyticRealization.channelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticRealizationGenerator.channelMap_preimage
    source
    target

/-- The analytic refinement-realization map has the refinement trace hom as preimage. -/
theorem TraceAnalyticRealization.refinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticRealizationGenerator.refinementMap_preimage
    source
    target

/-- The analytic schedule-realization map has the schedule trace hom as preimage. -/
theorem TraceAnalyticRealization.scheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticRealizationGenerator.scheduleMap_preimage
    source
    target

/-- The analytic weight-drop-realization map has the weight-drop trace hom as preimage. -/
theorem TraceAnalyticRealization.weightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticRealizationGenerator.weightDropMap_preimage
    source
    target

/-- The analytic Fubini-realization map has the Fubini trace hom as preimage. -/
theorem TraceAnalyticRealization.fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticRealizationGenerator.fubiniMap_preimage
    source
    target

/-- The analytic realization root exposes completed-zeta zero-pole residue soundness. -/
theorem TraceAnalyticRealization.completedZeta_zeroPole_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  TraceAnalyticSoundness.completedZeta_zeroPole_residueGenerator_sound
    f
    hPhi
    hR

/-- The analytic realization root exposes completed-zeta zero-pole channel soundness. -/
theorem TraceAnalyticRealization.completedZeta_zeroPole_channelGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  TraceAnalyticSoundness.completedZeta_zeroPole_channelGenerator_sound
    f
    F
    h
    u

/-- The analytic realization root exposes the rectangle-certified residue pipeline. -/
theorem TraceAnalyticRealization.completedZeta_zeroPole_residueRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  TraceAnalyticSoundness.completedZeta_zeroPole_residueRectanglePipeline_sound
    f
    hPhi
    hR

/-- The analytic realization root exposes the scheduled channel rectangle pipeline. -/
theorem TraceAnalyticRealization.completedZeta_zeroPole_channelRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  TraceAnalyticSoundness.completedZeta_zeroPole_channelRectanglePipeline_sound
    f
    F
    h
    u

/-- The analytic realization root exposes the first completed-zeta quotient relation. -/
theorem TraceAnalyticRealization.completedZeta_zeroPole_quotientClass_eq_empty :
    TraceCorQQuotient.ofCandidate
        completedZetaZeroPoleTraceCorQQuotientCandidate =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  TraceAnalyticSoundness.completedZeta_zeroPole_quotientClass_eq_empty

end AnalyticMotives
end LFunctions
end Boundary
