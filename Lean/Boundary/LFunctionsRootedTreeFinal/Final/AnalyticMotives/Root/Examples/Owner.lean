import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Examples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Examples.CompletedZeta.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Examples.Payload.Owner

/-!
# Top-root analytic motive examples

This file records the root import boundary for concrete examples and adapters
from existing analytic lanes into the analytic-motive trace calculus.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Example aggregate: completed-zeta residue rectangle soundness. -/
theorem AnalyticMotivesRoot.examples_completedZeta_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  AnalyticMotiveExamples.completedZeta_residueGenerator_sound
    f
    hPhi
    hR

/-- Example aggregate: completed-zeta channel rectangle soundness. -/
theorem AnalyticMotivesRoot.examples_completedZeta_channelGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  AnalyticMotiveExamples.completedZeta_channelGenerator_sound
    f
    F
    h
    u

/-- Example aggregate: completed-zeta residue rectangle hom recovers its trace hom. -/
theorem AnalyticMotivesRoot.examples_completedZeta_residueRectangleHom_traceHom
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).traceHom =
      completedZetaZeroPoleResidueRectanglePipeline_hom R :=
  AnalyticMotiveExamples.completedZeta_residueRectangleHom_traceHom
    R

/-- Example aggregate: completed-zeta scheduled-channel hom recovers its trace hom. -/
theorem AnalyticMotivesRoot.examples_completedZeta_channelRectangleHom_traceHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).traceHom =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u :=
  AnalyticMotiveExamples.completedZeta_channelRectangleHom_traceHom
    f
    F
    h
    u

/-- Example aggregate: completed-zeta residue rectangle source count is its rectangle-list length. -/
theorem AnalyticMotivesRoot.examples_completedZeta_residueRectangleSource_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangles.length :=
  AnalyticMotiveExamples.completedZeta_residueRectangleSource_importedRectangleCount_eq_length
    R

/-- Example aggregate: completed-zeta residue rectangle pullback-pushforward naturality. -/
theorem AnalyticMotivesRoot.examples_completedZeta_residueRectangleHom_pullbackPushforward_naturality
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
  AnalyticMotiveExamples.completedZeta_residueRectangleHom_pullbackPushforward_naturality
    R
    probe

end AnalyticMotives
end LFunctions
end Boundary
