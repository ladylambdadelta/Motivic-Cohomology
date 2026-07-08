import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.Payload.Owner

/-!
# Top-level completed-zeta finite-rectangle compact-geometric adapters

This directory exposes completed-zeta finite-rectangle compact-geometric
adapter facts at the top-level analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes the finite-rectangle residue compact morphism trace representative. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homTrace
    R

/-- The analytic-motives root exposes the finite-rectangle residue representable map. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_representableMap
    R

/-- The analytic-motives root exposes the finite-rectangle scheduled-channel compact morphism trace representative. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homTrace
    f
    F
    h
    u

/-- The analytic-motives root exposes the finite-rectangle scheduled-channel representable map. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_representableMap
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
