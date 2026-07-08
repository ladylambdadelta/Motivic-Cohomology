import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ResidueRectangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ChannelRectangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.FunctorBridges.Owner

/-!
# Completed-zeta finite-rectangle compact-generator adapters

This directory exposes the concrete finite-rectangle soundness seeds as
compact geometric analytic generators and compact-generator morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The soundness-seed residue compact morphism is represented by the residue pipeline hom. -/
theorem completedZetaFiniteRectangleSoundnessSeed_residueHom_traceHom
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_traceHom
    R

/-- The soundness-seed residue compact morphism induces the residue pipeline representable map. -/
theorem completedZetaFiniteRectangleSoundnessSeed_residueHom_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_representableMap
    R

/-- The soundness-seed residue compact morphism is recovered from its lifted Yoneda map. -/
theorem completedZetaFiniteRectangleSoundnessSeed_residueHom_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_yonedaPreimage
    R

/-- The soundness-seed scheduled-channel compact morphism is represented by the channel pipeline hom. -/
theorem completedZetaFiniteRectangleSoundnessSeed_channelHom_traceHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_traceHom
    f
    F
    h
    u

/-- The soundness-seed scheduled-channel compact morphism induces the channel pipeline representable map. -/
theorem completedZetaFiniteRectangleSoundnessSeed_channelHom_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_representableMap
    f
    F
    h
    u

/-- The soundness-seed scheduled-channel compact morphism is recovered from its lifted Yoneda map. -/
theorem completedZetaFiniteRectangleSoundnessSeed_channelHom_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_yonedaPreimage
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
