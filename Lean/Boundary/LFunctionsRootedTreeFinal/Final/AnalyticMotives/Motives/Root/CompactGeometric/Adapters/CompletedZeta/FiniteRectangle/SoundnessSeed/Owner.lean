import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Owner

/-!
# Motive-root completed-zeta finite-rectangle compact-geometric soundness seeds

This file exposes the completed-zeta residue and scheduled-channel
finite-rectangle compact-geometric adapter facts at the `TraceAnalyticMotive`
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The motive root exposes the residue rectangle compact source trace object. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_sourceTraceObject
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_source R :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_sourceTraceObject
    R

/-- The motive root exposes the residue rectangle compact target trace object. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_targetTraceObject :
    completedZetaZeroPoleResidueRectangleTargetGenerator.traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_targetTraceObject

/-- The motive root exposes the residue rectangle compact morphism trace representative. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTrace
    R

/-- The motive root exposes the residue rectangle representable map. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_representableMap
    R

/-- The motive root exposes residue rectangle Yoneda recovery. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_yonedaPreimage
    R

/-- The motive root exposes residue rectangle pipeline pullback. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_pullback
    (R : ℝ) (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      presheaf.pullback
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_pullback
    R
    presheaf

/-- The motive root exposes residue rectangle source imported-rectangle count. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_sourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_sourceImportedRectangleCount
    R

/-- The motive root exposes residue rectangle morphism source count-as-length. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homSourceRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceRectangleCount_eq_length
    R

/-- The motive root exposes residue rectangle pullback-pushforward naturality. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_pullbackPushforward_naturality
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
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_pullbackPushforward_naturality
    R
    probe

/-- The motive root exposes the scheduled-channel compact source trace object. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_sourceTraceObject
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_sourceTraceObject
    f
    F
    h
    u

/-- The motive root exposes the scheduled-channel compact target trace object. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_targetTraceObject :
    completedZetaZeroPoleChannelRectangleTargetGenerator.traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_targetTraceObject

/-- The motive root exposes the scheduled-channel compact morphism trace representative. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTrace
    f
    F
    h
    u

/-- The motive root exposes the scheduled-channel representable map. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_representableMap
    f
    F
    h
    u

/-- The motive root exposes scheduled-channel Yoneda recovery. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_yonedaPreimage
    f
    F
    h
    u

/-- The motive root exposes scheduled-channel pipeline pullback. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_pullback
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      presheaf.pullback
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_pullback
    f
    F
    h
    u
    presheaf

/-- The motive root exposes scheduled-channel source imported-rectangle count. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_sourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_sourceImportedRectangleCount
    f
    F
    h
    u

/-- The motive root exposes scheduled-channel morphism source count-as-length. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homSourceRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceRectangleCount_eq_length
    f
    F
    h
    u

/-- The motive root exposes scheduled-channel pullback-pushforward naturality. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_pullbackPushforward_naturality
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
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_pullbackPushforward_naturality
    f
    F
    h
    u
    probe

end AnalyticMotives
end LFunctions
end Boundary
