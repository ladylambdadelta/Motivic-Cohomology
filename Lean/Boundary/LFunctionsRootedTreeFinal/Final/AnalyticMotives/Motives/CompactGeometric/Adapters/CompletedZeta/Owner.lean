import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.Payload.Owner

/-!
# Completed-zeta compact-geometric adapters

This directory exposes completed-zeta analytic payload after it has been lifted
to compact geometric analytic generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The completed-zeta compact-geometric residue morphism is represented by the residue pipeline hom. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTrace
    R

/-- The completed-zeta compact-geometric residue morphism induces the residue representable map. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_representableMap
    R

/-- The completed-zeta compact-geometric scheduled-channel morphism is represented by the channel pipeline hom. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTrace
    f
    F
    h
    u

/-- The completed-zeta compact-geometric scheduled-channel morphism induces the channel representable map. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_representableMap
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
