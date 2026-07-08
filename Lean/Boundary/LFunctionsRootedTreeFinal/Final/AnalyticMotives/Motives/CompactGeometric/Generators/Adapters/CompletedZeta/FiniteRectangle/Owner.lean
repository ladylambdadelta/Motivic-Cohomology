import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Owner

/-!
# Completed-zeta finite-rectangle compact-generator adapters

This directory connects completed-zeta finite-rectangle analytic realization
data to the compact geometric analytic generator lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The finite-rectangle residue compact morphism is represented by the residue pipeline hom. -/
theorem completedZetaFiniteRectangle_residueHom_traceHom
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  completedZetaFiniteRectangleSoundnessSeed_residueHom_traceHom
    R

/-- The finite-rectangle residue compact morphism induces the residue pipeline representable map. -/
theorem completedZetaFiniteRectangle_residueHom_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  completedZetaFiniteRectangleSoundnessSeed_residueHom_representableMap
    R

/-- The finite-rectangle residue compact morphism is recovered from its lifted Yoneda map. -/
theorem completedZetaFiniteRectangle_residueHom_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  completedZetaFiniteRectangleSoundnessSeed_residueHom_yonedaPreimage
    R

/-- The finite-rectangle scheduled-channel compact morphism is represented by the channel pipeline hom. -/
theorem completedZetaFiniteRectangle_channelHom_traceHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  completedZetaFiniteRectangleSoundnessSeed_channelHom_traceHom
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism induces the channel pipeline representable map. -/
theorem completedZetaFiniteRectangle_channelHom_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  completedZetaFiniteRectangleSoundnessSeed_channelHom_representableMap
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism is recovered from its lifted Yoneda map. -/
theorem completedZetaFiniteRectangle_channelHom_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  completedZetaFiniteRectangleSoundnessSeed_channelHom_yonedaPreimage
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
