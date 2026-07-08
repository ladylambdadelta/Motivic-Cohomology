import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Payload.Owner

/-!
# Completed-zeta finite-rectangle compact-geometric soundness seeds

This file re-exposes the two concrete finite-rectangle completed-zeta seeds at
the compact geometric analytic motive boundary.  The underlying constructions
are owned by the compact-generator adapter branch; this file gives downstream
compact-geometric motive users a small public surface for the bridge.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact-geometric residue source is the zero-pole residue rectangle pipeline source. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_sourceTraceObject
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_source R :=
  completedZetaZeroPoleResidueRectangleSourceGenerator_traceObject
    R

/-- The compact-geometric residue target is the zero-pole residue rectangle pipeline target. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_targetTraceObject :
    completedZetaZeroPoleResidueRectangleTargetGenerator.traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  completedZetaZeroPoleResidueRectangleTargetGenerator_traceObject

/-- The compact-geometric residue morphism is represented by the residue rectangle pipeline hom. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_traceHom
    R

/-- The compact-geometric residue morphism induces the residue rectangle representable map. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_representableMap
    R

/-- The compact-geometric residue morphism is recovered from its lifted representable map. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_yonedaPreimage
    R

/-- Pullback along the compact-geometric residue morphism is pipeline pullback. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_pullback
    (R : ℝ) (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      presheaf.pullback
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_pullback
    R
    presheaf

/-- The compact-geometric residue source keeps the imported rectangle count of its pipeline source. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_sourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  completedZetaZeroPoleResidueRectangleSourceGenerator_importedRectangleCount
    R

/-- The compact-geometric residue morphism source endpoint is counted by its imported rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles.length :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_sourceImportedRectangleCount_eq_length
    R

/-- Residue pullback-precomposition commutes with residue pushforward-postcomposition. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_pullbackPushforward_naturality
    (R : ℝ)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        (completedZetaZeroPoleResidueRectangleSourceGenerator R)
        probe ≫
        TraceSixFunctorPushforward.representablePostcompositionOperator
          probeSource
          (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      TraceSixFunctorPushforward.representablePostcompositionOperator
          probeTarget
          (completedZetaZeroPoleResidueRectangleGeneratorHom R) ≫
        TraceSixFunctorPullback.representablePrecompositionOperator
          completedZetaZeroPoleResidueRectangleTargetGenerator
          probe :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_pullbackPushforward_naturality
    R
    probe

/-- The compact-geometric scheduled-channel source is the scheduled-channel rectangle pipeline source. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_sourceTraceObject
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u :=
  completedZetaZeroPoleChannelRectangleSourceGenerator_traceObject
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel target is the scheduled-channel rectangle pipeline target. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_targetTraceObject :
    completedZetaZeroPoleChannelRectangleTargetGenerator.traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  completedZetaZeroPoleChannelRectangleTargetGenerator_traceObject

/-- The compact-geometric scheduled-channel morphism is represented by the channel pipeline hom. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_traceHom
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism induces the channel representable map. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_representableMap
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

/-- The compact-geometric scheduled-channel morphism is recovered from its lifted representable map. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_yonedaPreimage
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

/-- Pullback along the compact-geometric scheduled-channel morphism is pipeline pullback. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_pullback
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      presheaf.pullback
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_pullback
    f
    F
    h
    u
    presheaf

/-- The compact-geometric scheduled-channel source keeps the rectangle count of its pipeline source. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_sourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  completedZetaZeroPoleChannelRectangleSourceGenerator_importedRectangleCount
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism source endpoint is counted by its rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles.length :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_sourceImportedRectangleCount_eq_length
    f
    F
    h
    u

/-- Channel pullback-precomposition commutes with channel pushforward-postcomposition. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_pullbackPushforward_naturality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)
        probe ≫
        TraceSixFunctorPushforward.representablePostcompositionOperator
          probeSource
          (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      TraceSixFunctorPushforward.representablePostcompositionOperator
          probeTarget
          (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) ≫
        TraceSixFunctorPullback.representablePrecompositionOperator
          completedZetaZeroPoleChannelRectangleTargetGenerator
          probe :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_pullbackPushforward_naturality
    f
    F
    h
    u
    probe

end AnalyticMotives
end LFunctions
end Boundary
