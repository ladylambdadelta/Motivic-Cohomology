import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.Payload.Owner

/-!
# Compact-geometric adapter facade

This directory exposes concrete analytic adapter constructions at the compact
geometric analytic motive boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact-geometric residue adapter morphism is represented by the residue pipeline hom. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTrace
    R

/-- The compact-geometric residue adapter morphism induces the residue representable map. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_representableMap
    R

/-- The compact-geometric scheduled-channel adapter morphism is represented by the channel pipeline hom. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTrace
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel adapter morphism induces the channel representable map. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_representableMap
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
