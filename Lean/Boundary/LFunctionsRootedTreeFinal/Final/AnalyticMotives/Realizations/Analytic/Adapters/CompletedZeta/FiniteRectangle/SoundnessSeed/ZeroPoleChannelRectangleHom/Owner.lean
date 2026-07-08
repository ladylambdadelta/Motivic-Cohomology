import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectangleTraceCorQ.Owner

/-!
# Zero-pole scheduled-rectangle channel typed homs

This file lifts the scheduled-rectangle channel generator from a raw
`TraceCorQ` formal sum to a typed hom in the trace-correspondence category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The typed source object for the scheduled-rectangle channel step. -/
def completedZetaZeroPoleChannelScheduledRectangleHomSource
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQObject :=
  completedZetaZeroPoleChannelPresentationWithScheduledRectangle f F h u

/-- The typed target object for the scheduled-rectangle channel step. -/
def completedZetaZeroPoleChannelScheduledRectangleHomTarget :
    TraceCorQObject :=
  completedZetaZeroPoleChannelOutput

/-- The typed source object carries the scheduled rectangle presentation ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectangleHomSource_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleHomSource
      f F h u).certificateLedger =
      (completedZetaZeroPoleChannelPresentationWithScheduledRectangle
        f F h u).certificateLedger :=
  rfl

/-- The typed source object imports the scheduled rectangle presentation payload. -/
theorem completedZetaZeroPoleChannelScheduledRectangleHomSource_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleHomSource
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelPresentationWithScheduledRectangle
        f F h u).importedRectangleCount :=
  rfl

/-- The typed source object keeps the scheduled rectangle presentation bookkeeping payload. -/
theorem completedZetaZeroPoleChannelScheduledRectangleHomSource_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleHomSource
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelPresentationWithScheduledRectangle
        f F h u).traceBookkeepingCount :=
  rfl

/-- The typed target object is the certified channel output. -/
theorem completedZetaZeroPoleChannelScheduledRectangleHomTarget_eq_channelOutput :
    completedZetaZeroPoleChannelScheduledRectangleHomTarget =
      completedZetaZeroPoleChannelOutput :=
  rfl

/-- The scheduled-rectangle channel generator as a typed hom term. -/
def completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHomTerm
      (completedZetaZeroPoleChannelScheduledRectangleHomSource f F h u)
      completedZetaZeroPoleChannelScheduledRectangleHomTarget :=
  TraceCorQHomTerm.ofGenerator
    (completedZetaZeroPoleChannelScheduledRectangleHomSource f F h u)
    completedZetaZeroPoleChannelScheduledRectangleHomTarget
    1
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator f F h u)
    rfl
    rfl

/-- The typed scheduled-rectangle channel term has coefficient one. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm_coefficient
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm
      f F h u).coefficient =
      1 :=
  rfl

/-- The typed scheduled-rectangle channel term has the scheduled-rectangle generator. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm_generator
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm
      f F h u).generator =
      completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator f F h u :=
  rfl

/-- The typed scheduled-rectangle channel term carries the generator certificate ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm
      f F h u).certificateLedger =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).certificateLedger :=
  rfl

/-- The typed scheduled-rectangle channel term carries the generator imported payload. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).importedRectangleCount :=
  rfl

/-- The typed scheduled-rectangle channel term carries the generator bookkeeping payload. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).traceBookkeepingCount :=
  rfl

/-- The typed scheduled-rectangle channel term carries the generator rewrite-step payload. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).rewriteStepCount :=
  rfl

/-- The scheduled-rectangle channel generator as a typed singleton formal sum. -/
def completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHomFormalSum
      (completedZetaZeroPoleChannelScheduledRectangleHomSource f F h u)
      completedZetaZeroPoleChannelScheduledRectangleHomTarget :=
  TraceCorQHomFormalSum.singleton
    (completedZetaZeroPoleChannelScheduledRectangleHomSource f F h u)
    completedZetaZeroPoleChannelScheduledRectangleHomTarget
    1
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator f F h u)
    rfl
    rfl

/-- Forgetting endpoint proofs recovers the raw scheduled-rectangle channel singleton. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_raw
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
      f F h u).raw =
      completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
        f F h u :=
  rfl

/-- The typed singleton carries the same certificate ledger as the raw scheduled singleton. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
      f F h u).certificateLedger =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
        f F h u).certificateLedger :=
  congrArg
    TraceCorQFormalSum.certificateLedger
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_raw
      f F h u)

/-- The typed singleton carries the same imported payload as the raw scheduled singleton. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
        f F h u).importedRectangleCount :=
  congrArg
    TraceCorQFormalSum.importedRectangleCount
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_raw
      f F h u)

/-- The typed singleton carries the same rectangle list as the raw scheduled singleton. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
        f F h u).importedRectangles :=
  congrArg
    TraceCorQFormalSum.importedRectangles
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_raw
      f F h u)

/-- The typed singleton carries the same bookkeeping payload as the raw scheduled singleton. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
        f F h u).traceBookkeepingCount :=
  congrArg
    TraceCorQFormalSum.traceBookkeepingCount
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_raw
      f F h u)

/-- The typed singleton carries the same rewrite-step payload as the raw scheduled singleton. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
        f F h u).rewriteStepCount :=
  congrArg
    TraceCorQFormalSum.rewriteStepCount
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_raw
      f F h u)

/-- The scheduled-rectangle channel typed hom class. -/
def completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHom
      (completedZetaZeroPoleChannelScheduledRectangleHomSource f F h u)
      completedZetaZeroPoleChannelScheduledRectangleHomTarget :=
  TraceCorQHom.ofFormalSum
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
      f F h u)

/-- The typed hom is represented by the scheduled-rectangle singleton formal sum. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom_eq_ofFormalSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom f F h u =
      TraceCorQHom.ofFormalSum
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
          f F h u) :=
  rfl

/-- The scheduled-rectangle channel typed hom is sound at its schedule parameter. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator_sound
    f F h u

end AnalyticMotives
end LFunctions
end Boundary
