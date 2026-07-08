import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Adapters.CompletedZeta.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Examples.CompletedZeta.Payload.Owner

/-!
# Completed-zeta adapter

This file collects example-level projections for the adapter from the RH lane's
completed-zeta contour calculus into the general residue-channel trace
presentation and compact-generator motive lane.

The concrete imports live in the analytic realization adapter branch, where the
completed-zeta finite-rectangle contour calculus is treated as an analytic
realization source for the synthetic trace computad, and in the compact
geometric generator adapter branch, where those certified trace presentations
become compact analytic generators and morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The completed-zeta example exposes residue-generator soundness through the realization root. -/
theorem completedZetaExample_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  TraceRealizations.completedZeta_zeroPole_residueGenerator_sound
    f
    hPhi
    hR

/-- The completed-zeta example exposes channel-generator soundness through the realization root. -/
theorem completedZetaExample_channelGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  TraceRealizations.completedZeta_zeroPole_channelGenerator_sound
    f
    F
    h
    u

/-- The completed-zeta example exposes the first quotient relation through the realization root. -/
theorem completedZetaExample_quotientClass_eq_empty :
    TraceCorQQuotient.ofCandidate
        completedZetaZeroPoleTraceCorQQuotientCandidate =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  TraceRealizations.completedZeta_zeroPole_quotientClass_eq_empty

/-- The residue rectangle example source imports exactly its listed rectangle certificates. -/
theorem completedZetaExample_residueRectangleSource_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectangleSourceGenerator R)

/-- The residue rectangle example source is the compact root residue rectangle source. -/
theorem completedZetaExample_residueRectangleSource_traceObject
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).traceObject =
      completedZetaZeroPoleResidueRectanglePipeline_source R :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_sourceTraceObject
    R

/-- The residue rectangle example morphism is represented by the compact root residue hom. -/
theorem completedZetaExample_residueRectangleHom_traceHom
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homTrace
    R

/-- The residue rectangle example morphism induces the root representable map. -/
theorem completedZetaExample_residueRectangleHom_representableMap
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_representableMap
    R

/-- The residue rectangle example morphism is recovered by Yoneda preimage. -/
theorem completedZetaExample_residueRectangleHom_yonedaPreimage
    (R : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleResidueRectangleGeneratorHom R).representableObjectMap =
      completedZetaZeroPoleResidueRectangleGeneratorHom R :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_yonedaPreimage
    R

/-- Pullback along the residue rectangle example morphism is pipeline pullback. -/
theorem completedZetaExample_residueRectangleHom_pullback
    (R : ℝ) (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleResidueRectangleGeneratorHom R) =
      presheaf.pullback
        (completedZetaZeroPoleResidueRectanglePipeline_hom R) :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_pullback
    R
    presheaf

/-- The residue rectangle example morphism source imports exactly its listed rectangles. -/
theorem completedZetaExample_residueRectangleHom_sourceImportedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles.length :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceRectangleCount_eq_length
    R

/-- The residue rectangle example satisfies pullback-pushforward naturality. -/
theorem completedZetaExample_residueRectangleHom_pullbackPushforward_naturality
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
  AnalyticMotivesRoot.completedZetaResidueRectangle_pullbackPushforward_naturality
    R
    probe

/-- The scheduled-channel example source imports exactly its listed rectangle certificates. -/
theorem completedZetaExample_channelRectangleSource_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)

/-- The scheduled-channel example source is the compact root channel rectangle source. -/
theorem completedZetaExample_channelRectangleSource_traceObject
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).traceObject =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_sourceTraceObject
    f
    F
    h
    u

/-- The scheduled-channel example morphism is represented by the compact root channel hom. -/
theorem completedZetaExample_channelRectangleHom_traceHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homTrace
    f
    F
    h
    u

/-- The scheduled-channel example morphism induces the root representable map. -/
theorem completedZetaExample_channelRectangleHom_representableMap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableMap =
      TraceCorQPresheaf.representableMap
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_representableMap
    f
    F
    h
    u

/-- The scheduled-channel example morphism is recovered by Yoneda preimage. -/
theorem completedZetaExample_channelRectangleHom_yonedaPreimage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).representableObjectMap =
      completedZetaZeroPoleChannelRectangleGeneratorHom f F h u :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_yonedaPreimage
    f
    F
    h
    u

/-- Pullback along the scheduled-channel example morphism is pipeline pullback. -/
theorem completedZetaExample_channelRectangleHom_pullback
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (presheaf : TraceCorQPresheaf) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u) =
      presheaf.pullback
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_pullback
    f
    F
    h
    u
    presheaf

/-- The scheduled-channel example morphism source imports exactly its listed rectangles. -/
theorem completedZetaExample_channelRectangleHom_sourceImportedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles.length :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceRectangleCount_eq_length
    f
    F
    h
    u

/-- The scheduled-channel example satisfies pullback-pushforward naturality. -/
theorem completedZetaExample_channelRectangleHom_pullbackPushforward_naturality
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
  AnalyticMotivesRoot.completedZetaChannelRectangle_pullbackPushforward_naturality
    f
    F
    h
    u
    probe

end AnalyticMotives
end LFunctions
end Boundary
