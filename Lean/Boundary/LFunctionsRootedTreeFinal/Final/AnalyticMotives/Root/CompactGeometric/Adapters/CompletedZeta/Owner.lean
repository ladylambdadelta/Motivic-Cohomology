import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Adapters.CompletedZeta.Payload.Owner

/-!
# Top-level completed-zeta compact-geometric adapters

This directory exposes completed-zeta compact-geometric adapter facts at the
top-level analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes the completed-zeta residue compact adapter trace representative. -/
theorem AnalyticMotivesRoot.completedZetaAdapterResidue_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homTrace
    R

/-- The analytic-motives root exposes the completed-zeta residue compact adapter representable map. -/
theorem AnalyticMotivesRoot.completedZetaAdapterResidue_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_representableMap
    R

/-- The analytic-motives root exposes the completed-zeta scheduled-channel compact adapter trace representative. -/
theorem AnalyticMotivesRoot.completedZetaAdapterChannel_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homTrace
    f
    F
    h
    u

/-- The analytic-motives root exposes the completed-zeta scheduled-channel compact adapter representable map. -/
theorem AnalyticMotivesRoot.completedZetaAdapterChannel_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_representableMap
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
