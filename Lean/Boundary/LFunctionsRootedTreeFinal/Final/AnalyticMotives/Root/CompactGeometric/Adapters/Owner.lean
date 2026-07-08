import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Adapters.CompletedZeta.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Adapters.Payload.Owner

/-!
# Top-level compact-geometric adapter facade

This directory exposes compact-geometric analytic adapter facts at the
top-level analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes the compact-geometric residue adapter trace representative. -/
theorem AnalyticMotivesRoot.adapterResidue_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  AnalyticMotivesRoot.completedZetaAdapterResidue_homTrace
    R

/-- The analytic-motives root exposes the compact-geometric residue adapter representable map. -/
theorem AnalyticMotivesRoot.adapterResidue_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  AnalyticMotivesRoot.completedZetaAdapterResidue_representableMap
    R

/-- The analytic-motives root exposes the compact-geometric scheduled-channel adapter trace representative. -/
theorem AnalyticMotivesRoot.adapterChannel_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  AnalyticMotivesRoot.completedZetaAdapterChannel_homTrace
    f
    F
    h
    u

/-- The analytic-motives root exposes the compact-geometric scheduled-channel adapter representable map. -/
theorem AnalyticMotivesRoot.adapterChannel_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  AnalyticMotivesRoot.completedZetaAdapterChannel_representableMap
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
