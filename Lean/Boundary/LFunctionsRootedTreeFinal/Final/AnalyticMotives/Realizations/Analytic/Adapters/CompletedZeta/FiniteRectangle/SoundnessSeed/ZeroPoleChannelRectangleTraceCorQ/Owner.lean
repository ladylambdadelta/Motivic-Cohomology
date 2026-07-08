import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectangleCertificates.Owner

/-!
# Zero-pole scheduled-rectangle channel trace correspondences

This file exposes the scheduled-rectangle channel transport as a raw
`TraceCorQ` generator and singleton formal sum.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The scheduled-rectangle channel transport as a trace-correspondence generator. -/
def completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQGenerator :=
  completedZetaZeroPoleChannelTransportWithScheduledRectangle f F h u

/-- The scheduled-rectangle channel generator starts at the certified scheduled presentation. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_source
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u).source =
      completedZetaZeroPoleChannelPresentationWithScheduledRectangle f F h u :=
  rfl

/-- The scheduled-rectangle channel generator targets the certified channel output. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_target
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u).target =
      completedZetaZeroPoleChannelOutput :=
  rfl

/-- The scheduled-rectangle channel generator carries the channel rewrite path. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_path
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u).path =
      completedZetaZeroPoleChannelPath :=
  rfl

/-- The scheduled-rectangle channel generator certificate ledger splits by source, target, and path. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_certificateLedger_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u).certificateLedger =
      ResidueChannelCertificateLedger.append
        (completedZetaZeroPoleChannelPresentationWithScheduledRectangle
          f F h u).certificateLedger
        (ResidueChannelCertificateLedger.append
          completedZetaZeroPoleChannelOutput.certificateLedger
          (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
            f F h u).pathCertificateLedger) :=
  TraceCorQGenerator.certificateLedger_eq_source_target_path
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u)

/-- The scheduled-rectangle channel generator imports source, target, and path payload. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_importedRectangleCount_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelPresentationWithScheduledRectangle
        f F h u).importedRectangleCount +
        (completedZetaZeroPoleChannelOutput.importedRectangleCount +
          (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
            f F h u).pathCertificateLedger.importedRectangleCount) :=
  TraceCorQGenerator.importedRectangleCount_eq_source_target_path
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u)

/-- The scheduled-rectangle channel generator exposes source, target, and path rectangle lists. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_importedRectangles_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelPresentationWithScheduledRectangle
        f F h u).importedRectangles ++
        (completedZetaZeroPoleChannelOutput.importedRectangles ++
          (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
            f F h u).pathCertificateLedger.importedRectangles) :=
  TraceCorQGenerator.importedRectangles_eq_source_target_path
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u)

/-- The scheduled-rectangle channel generator keeps source, target, and path bookkeeping. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_traceBookkeepingCount_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelPresentationWithScheduledRectangle
        f F h u).traceBookkeepingCount +
        (completedZetaZeroPoleChannelOutput.traceBookkeepingCount +
          (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
            f F h u).pathCertificateLedger.traceBookkeepingCount) :=
  TraceCorQGenerator.traceBookkeepingCount_eq_source_target_path
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u)

/-- The scheduled-rectangle channel generator keeps source, target, and path rewrite steps. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_rewriteStepCount_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelPresentationWithScheduledRectangle
        f F h u).rewriteStepCount +
        (completedZetaZeroPoleChannelOutput.rewriteStepCount +
          (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
            f F h u).pathCertificateLedger.rewriteStepCount) :=
  TraceCorQGenerator.rewriteStepCount_eq_source_target_path
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u)

/-- The scheduled-rectangle channel generator is analytically sound at its schedule parameter. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaZeroPoleChannelTransportWithScheduledRectangle_sound
    f F h u

/-- The singleton Q-linear correspondence generated by the scheduled-rectangle channel step. -/
def completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQFormalSum :=
  TraceCorQFormalSum.singleton
    1
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator f F h u)

/-- The scheduled-rectangle channel singleton carries the generator certificate ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
      f F h u).certificateLedger =
      ResidueChannelCertificateLedger.append
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
          f F h u).certificateLedger
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- The scheduled-rectangle channel singleton imports the generator payload plus zero. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).importedRectangleCount +
        0 :=
  Eq.trans
    (TraceCorQFormalSum.singleton_importedRectangleCount
      1
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u))
    (congrArg
      (fun count =>
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
          f F h u).importedRectangleCount + count)
      ResidueChannelCertificateLedger.empty_importedRectangleCount)

/-- The scheduled-rectangle channel singleton exposes the generator rectangle list plus the empty tail. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).importedRectangles ++
        ResidueChannelCertificateLedger.empty.importedRectangles :=
  TraceCorQFormalSum.singleton_importedRectangles
    1
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
      f F h u)

/-- The scheduled-rectangle channel singleton keeps the generator bookkeeping plus zero. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).traceBookkeepingCount +
        0 :=
  Eq.trans
    (TraceCorQFormalSum.singleton_traceBookkeepingCount
      1
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u))
    (congrArg
      (fun count =>
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
          f F h u).traceBookkeepingCount + count)
      ResidueChannelCertificateLedger.empty_traceBookkeepingCount)

/-- The scheduled-rectangle channel singleton keeps the generator rewrite steps plus zero. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).rewriteStepCount +
        0 :=
  Eq.trans
    (TraceCorQFormalSum.singleton_rewriteStepCount
      1
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u))
    (congrArg
      (fun count =>
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
          f F h u).rewriteStepCount + count)
      ResidueChannelCertificateLedger.empty_rewriteStepCount)

end AnalyticMotives
end LFunctions
end Boundary
