import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.Payload.Owner

/-!
# Completed-zeta finite-rectangle compact-geometric adapters

This directory exposes finite-rectangle completed-zeta payload at the compact
geometric analytic motive boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The finite-rectangle compact-geometric residue morphism is represented by the residue pipeline hom. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTrace
    R

/-- The finite-rectangle compact-geometric residue morphism induces the residue representable map. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_representableMap
    R

/-- The finite-rectangle compact-geometric scheduled-channel morphism is represented by the channel pipeline hom. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTrace
    f
    F
    h
    u

/-- The finite-rectangle compact-geometric scheduled-channel morphism induces the channel representable map. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_representableMap
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
