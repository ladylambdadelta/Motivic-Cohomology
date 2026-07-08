import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Examples.CompletedZeta.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Examples.Payload.Owner

/-!
# Analytic motive examples and adapters

This directory is for adapters from existing analytic lanes into the general
analytic-motive trace calculus.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The examples root exposes completed-zeta residue-generator soundness. -/
theorem AnalyticMotiveExamples.completedZeta_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaExample_residueGenerator_sound
    f
    hPhi
    hR

/-- The examples root exposes completed-zeta channel-generator soundness. -/
theorem AnalyticMotiveExamples.completedZeta_channelGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaExample_channelGenerator_sound
    f
    F
    h
    u

/-- The examples root exposes the first completed-zeta quotient relation. -/
theorem AnalyticMotiveExamples.completedZeta_quotientClass_eq_empty :
    TraceCorQQuotient.ofCandidate
        completedZetaZeroPoleTraceCorQQuotientCandidate =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  completedZetaExample_quotientClass_eq_empty

/-- The examples root exposes the completed-zeta residue rectangle compact source. -/
theorem AnalyticMotiveExamples.completedZeta_residueRectangleSource_traceObject
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_source R :=
  completedZetaExample_residueRectangleSource_traceObject
    R

/-- The examples root exposes the completed-zeta residue rectangle compact morphism representative. -/
theorem AnalyticMotiveExamples.completedZeta_residueRectangleHom_traceHom
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  completedZetaExample_residueRectangleHom_traceHom
    R

/-- The examples root exposes the residue rectangle representable map. -/
theorem AnalyticMotiveExamples.completedZeta_residueRectangleHom_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  completedZetaExample_residueRectangleHom_representableMap
    R

/-- The examples root exposes residue rectangle Yoneda recovery. -/
theorem AnalyticMotiveExamples.completedZeta_residueRectangleHom_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  completedZetaExample_residueRectangleHom_yonedaPreimage
    R

/-- The examples root exposes residue rectangle pipeline pullback. -/
theorem AnalyticMotiveExamples.completedZeta_residueRectangleHom_pullback
    (R : ℝ) (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      presheaf.pullback
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  completedZetaExample_residueRectangleHom_pullback
    R
    presheaf

/-- The examples root exposes residue rectangle source imported-rectangle count-as-length. -/
theorem AnalyticMotiveExamples.completedZeta_residueRectangleSource_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangles.length :=
  completedZetaExample_residueRectangleSource_importedRectangleCount_eq_length
    R

/-- The examples root exposes residue rectangle hom source imported-rectangle count-as-length. -/
theorem AnalyticMotiveExamples.completedZeta_residueRectangleHom_sourceImportedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles.length :=
  completedZetaExample_residueRectangleHom_sourceImportedRectangleCount_eq_length
    R

/-- The examples root exposes residue rectangle pullback-pushforward naturality. -/
theorem AnalyticMotiveExamples.completedZeta_residueRectangleHom_pullbackPushforward_naturality
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
  completedZetaExample_residueRectangleHom_pullbackPushforward_naturality
    R
    probe

/-- The examples root exposes the completed-zeta scheduled-channel compact source. -/
theorem AnalyticMotiveExamples.completedZeta_channelRectangleSource_traceObject
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u :=
  completedZetaExample_channelRectangleSource_traceObject
    f
    F
    h
    u

/-- The examples root exposes the completed-zeta scheduled-channel compact morphism representative. -/
theorem AnalyticMotiveExamples.completedZeta_channelRectangleHom_traceHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  completedZetaExample_channelRectangleHom_traceHom
    f
    F
    h
    u

/-- The examples root exposes the scheduled-channel representable map. -/
theorem AnalyticMotiveExamples.completedZeta_channelRectangleHom_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  completedZetaExample_channelRectangleHom_representableMap
    f
    F
    h
    u

/-- The examples root exposes scheduled-channel Yoneda recovery. -/
theorem AnalyticMotiveExamples.completedZeta_channelRectangleHom_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  completedZetaExample_channelRectangleHom_yonedaPreimage
    f
    F
    h
    u

/-- The examples root exposes scheduled-channel pipeline pullback. -/
theorem AnalyticMotiveExamples.completedZeta_channelRectangleHom_pullback
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      presheaf.pullback
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  completedZetaExample_channelRectangleHom_pullback
    f
    F
    h
    u
    presheaf

/-- The examples root exposes scheduled-channel source imported-rectangle count-as-length. -/
theorem AnalyticMotiveExamples.completedZeta_channelRectangleSource_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangles.length :=
  completedZetaExample_channelRectangleSource_importedRectangleCount_eq_length
    f
    F
    h
    u

/-- The examples root exposes scheduled-channel hom source imported-rectangle count-as-length. -/
theorem AnalyticMotiveExamples.completedZeta_channelRectangleHom_sourceImportedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles.length :=
  completedZetaExample_channelRectangleHom_sourceImportedRectangleCount_eq_length
    f
    F
    h
    u

/-- The examples root exposes scheduled-channel pullback-pushforward naturality. -/
theorem AnalyticMotiveExamples.completedZeta_channelRectangleHom_pullbackPushforward_naturality
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
  completedZetaExample_channelRectangleHom_pullbackPushforward_naturality
    f
    F
    h
    u
    probe

end AnalyticMotives
end LFunctions
end Boundary
