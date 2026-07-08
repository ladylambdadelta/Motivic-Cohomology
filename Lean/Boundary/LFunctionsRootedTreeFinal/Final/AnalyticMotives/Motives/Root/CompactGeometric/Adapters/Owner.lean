import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.CompletedZeta.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.Payload.Owner

/-!
# Motive-root compact-geometric adapter facade

This directory exposes compact-geometric analytic adapter facts at the motive
root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The motive root exposes the compact-geometric residue adapter trace representative. -/
theorem TraceAnalyticMotive.adapterResidue_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  TraceAnalyticMotive.completedZetaAdapterResidue_homTrace
    R

/-- The motive root exposes the compact-geometric residue adapter representable map. -/
theorem TraceAnalyticMotive.adapterResidue_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticMotive.completedZetaAdapterResidue_representableMap
    R

/-- The motive root exposes the compact-geometric scheduled-channel adapter trace representative. -/
theorem TraceAnalyticMotive.adapterChannel_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  TraceAnalyticMotive.completedZetaAdapterChannel_homTrace
    f
    F
    h
    u

/-- The motive root exposes the compact-geometric scheduled-channel adapter representable map. -/
theorem TraceAnalyticMotive.adapterChannel_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  TraceAnalyticMotive.completedZetaAdapterChannel_representableMap
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
