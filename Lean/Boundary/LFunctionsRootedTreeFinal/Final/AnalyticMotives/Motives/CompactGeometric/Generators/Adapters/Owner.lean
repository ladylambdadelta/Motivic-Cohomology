import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.Owner

/-!
# Compact-generator analytic realization adapters

This directory owns concrete adapters from analytic realization data into the
compact geometric analytic generator lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact-generator residue adapter morphism is represented by the residue pipeline hom. -/
theorem compactGeneratorAdapter_residueHom_traceHom
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  completedZetaCompactGeneratorAdapter_residueHom_traceHom
    R

/-- The compact-generator residue adapter morphism induces the residue pipeline representable map. -/
theorem compactGeneratorAdapter_residueHom_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  completedZetaCompactGeneratorAdapter_residueHom_representableMap
    R

/-- The compact-generator residue adapter morphism is recovered from its lifted Yoneda map. -/
theorem compactGeneratorAdapter_residueHom_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  completedZetaCompactGeneratorAdapter_residueHom_yonedaPreimage
    R

/-- The compact-generator scheduled-channel adapter morphism is represented by the channel pipeline hom. -/
theorem compactGeneratorAdapter_channelHom_traceHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  completedZetaCompactGeneratorAdapter_channelHom_traceHom
    f
    F
    h
    u

/-- The compact-generator scheduled-channel adapter morphism induces the channel pipeline representable map. -/
theorem compactGeneratorAdapter_channelHom_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  completedZetaCompactGeneratorAdapter_channelHom_representableMap
    f
    F
    h
    u

/-- The compact-generator scheduled-channel adapter morphism is recovered from its lifted Yoneda map. -/
theorem compactGeneratorAdapter_channelHom_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  completedZetaCompactGeneratorAdapter_channelHom_yonedaPreimage
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
