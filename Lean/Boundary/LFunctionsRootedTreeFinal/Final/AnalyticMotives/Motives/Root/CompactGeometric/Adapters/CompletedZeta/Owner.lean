import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.CompletedZeta.Payload.Owner

/-!
# Motive-root completed-zeta compact-geometric adapters

This directory exposes completed-zeta compact-geometric adapter facts at the
motive root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The motive root exposes the completed-zeta residue compact adapter trace representative. -/
theorem TraceAnalyticMotive.completedZetaAdapterResidue_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homTrace
    R

/-- The motive root exposes the completed-zeta residue compact adapter representable map. -/
theorem TraceAnalyticMotive.completedZetaAdapterResidue_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_representableMap
    R

/-- The motive root exposes the completed-zeta scheduled-channel compact adapter trace representative. -/
theorem TraceAnalyticMotive.completedZetaAdapterChannel_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homTrace
    f
    F
    h
    u

/-- The motive root exposes the completed-zeta scheduled-channel compact adapter representable map. -/
theorem TraceAnalyticMotive.completedZetaAdapterChannel_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_representableMap
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
