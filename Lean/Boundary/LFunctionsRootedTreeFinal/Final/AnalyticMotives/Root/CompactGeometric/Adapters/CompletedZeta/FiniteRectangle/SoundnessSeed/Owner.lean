import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Owner

/-!
# Top-level completed-zeta finite-rectangle compact-geometric soundness seeds

This file re-exposes the completed-zeta residue and scheduled-channel
finite-rectangle compact-geometric adapter facts at the top-level
`AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes the residue rectangle compact source trace object. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_sourceTraceObject
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_source R :=
  TraceAnalyticMotive.completedZetaResidueRectangle_sourceTraceObject
    R

/-- The analytic-motives root exposes the residue rectangle compact target trace object. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_targetTraceObject :
    completedZetaZeroPoleResidueRectangleTargetGenerator.traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  TraceAnalyticMotive.completedZetaResidueRectangle_targetTraceObject

/-- The analytic-motives root exposes the residue rectangle compact morphism trace representative. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homTrace
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homTrace
    R

/-- The analytic-motives root exposes the residue rectangle representable map. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticMotive.completedZetaResidueRectangle_representableMap
    R

/-- The analytic-motives root exposes residue rectangle Yoneda recovery. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  TraceAnalyticMotive.completedZetaResidueRectangle_yonedaPreimage
    R

/-- The analytic-motives root exposes residue rectangle pipeline pullback. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_pullback
    (R : ℝ) (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      presheaf.pullback
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  TraceAnalyticMotive.completedZetaResidueRectangle_pullback
    R
    presheaf

/-- The analytic-motives root exposes residue rectangle source imported-rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_sourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  TraceAnalyticMotive.completedZetaResidueRectangle_sourceImportedRectangleCount
    R

/-- The analytic-motives root exposes residue rectangle morphism source count-as-length. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles.length :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homSourceRectangleCount_eq_length
    R

/-- The analytic-motives root exposes residue rectangle pullback-pushforward naturality. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_pullbackPushforward_naturality
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
  TraceAnalyticMotive.completedZetaResidueRectangle_pullbackPushforward_naturality
    R
    probe

/-- The analytic-motives root exposes the scheduled-channel compact source trace object. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_sourceTraceObject
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u :=
  TraceAnalyticMotive.completedZetaChannelRectangle_sourceTraceObject
    f
    F
    h
    u

/-- The analytic-motives root exposes the scheduled-channel compact target trace object. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_targetTraceObject :
    completedZetaZeroPoleChannelRectangleTargetGenerator.traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  TraceAnalyticMotive.completedZetaChannelRectangle_targetTraceObject

/-- The analytic-motives root exposes the scheduled-channel compact morphism trace representative. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homTrace
    f
    F
    h
    u

/-- The analytic-motives root exposes the scheduled-channel representable map. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_representableMap
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

/-- The analytic-motives root exposes scheduled-channel Yoneda recovery. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  TraceAnalyticMotive.completedZetaChannelRectangle_yonedaPreimage
    f
    F
    h
    u

/-- The analytic-motives root exposes scheduled-channel pipeline pullback. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_pullback
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      presheaf.pullback
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  TraceAnalyticMotive.completedZetaChannelRectangle_pullback
    f
    F
    h
    u
    presheaf

/-- The analytic-motives root exposes scheduled-channel source imported-rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_sourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  TraceAnalyticMotive.completedZetaChannelRectangle_sourceImportedRectangleCount
    f
    F
    h
    u

/-- The analytic-motives root exposes scheduled-channel morphism source count-as-length. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles.length :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homSourceRectangleCount_eq_length
    f
    F
    h
    u

/-- The analytic-motives root exposes scheduled-channel pullback-pushforward naturality. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_pullbackPushforward_naturality
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
  TraceAnalyticMotive.completedZetaChannelRectangle_pullbackPushforward_naturality
    f
    F
    h
    u
    probe

end AnalyticMotives
end LFunctions
end Boundary
