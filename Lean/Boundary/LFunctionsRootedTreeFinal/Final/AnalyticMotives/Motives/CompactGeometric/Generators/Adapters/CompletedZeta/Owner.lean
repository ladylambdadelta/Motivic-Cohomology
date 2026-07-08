import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.Owner

/-!
# Completed-zeta compact-generator adapters

This directory owns compact-generator adapters for completed-zeta analytic
realization data.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The completed-zeta residue compact morphism is represented by the residue pipeline hom. -/
theorem completedZetaCompactGeneratorAdapter_residueHom_traceHom
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  completedZetaFiniteRectangle_residueHom_traceHom
    R

/-- The completed-zeta residue compact morphism induces the residue pipeline representable map. -/
theorem completedZetaCompactGeneratorAdapter_residueHom_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  completedZetaFiniteRectangle_residueHom_representableMap
    R

/-- The completed-zeta residue compact morphism is recovered from its lifted Yoneda map. -/
theorem completedZetaCompactGeneratorAdapter_residueHom_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  completedZetaFiniteRectangle_residueHom_yonedaPreimage
    R

/-- The completed-zeta scheduled-channel compact morphism is represented by the channel pipeline hom. -/
theorem completedZetaCompactGeneratorAdapter_channelHom_traceHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  completedZetaFiniteRectangle_channelHom_traceHom
    f
    F
    h
    u

/-- The completed-zeta scheduled-channel compact morphism induces the channel pipeline representable map. -/
theorem completedZetaCompactGeneratorAdapter_channelHom_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  completedZetaFiniteRectangle_channelHom_representableMap
    f
    F
    h
    u

/-- The completed-zeta scheduled-channel compact morphism is recovered from its lifted Yoneda map. -/
theorem completedZetaCompactGeneratorAdapter_channelHom_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  completedZetaFiniteRectangle_channelHom_yonedaPreimage
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
