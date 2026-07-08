import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.Payload.Owner

/-!
# Motive-root completed-zeta finite-rectangle compact-geometric adapters

This directory exposes completed-zeta finite-rectangle compact-geometric
adapter facts at the motive root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The motive root exposes the finite-rectangle residue compact morphism trace representative. -/
theorem TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homTrace
    R

/-- The motive root exposes the finite-rectangle residue representable map. -/
theorem TraceAnalyticMotive.completedZetaFiniteRectangleResidue_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticMotive.completedZetaResidueRectangle_representableMap
    R

/-- The motive root exposes the finite-rectangle scheduled-channel compact morphism trace representative. -/
theorem TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homTrace
    f
    F
    h
    u

/-- The motive root exposes the finite-rectangle scheduled-channel representable map. -/
theorem TraceAnalyticMotive.completedZetaFiniteRectangleChannel_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  TraceAnalyticMotive.completedZetaChannelRectangle_representableMap
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
