import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectangleHom.Owner

/-!
# Zero-pole scheduled-rectangle channel representatives

This file records the explicit pre-quotient representative and ambient
quotient candidate underlying the scheduled-rectangle channel hom.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The explicit representative of the scheduled-rectangle channel hom. -/
def completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHomRepresentative
      (completedZetaZeroPoleChannelScheduledRectangleHomSource f F h u)
      completedZetaZeroPoleChannelScheduledRectangleHomTarget :=
  TraceCorQHomRepresentative.ofFormalSumLedger
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
      f F h u)
    TraceCorQRelationLedger.empty

/-- The scheduled-rectangle channel representative has the singleton typed formal sum. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative_formalSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
      f F h u).formalSum =
      completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
        f F h u :=
  rfl

/-- The scheduled-rectangle channel representative has empty relation ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative_ledger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
      f F h u).ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- The representative records formal-sum certificates and the empty ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
      f F h u).certificateLedger =
      ResidueChannelCertificateLedger.append
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
          f F h u).certificateLedger
        TraceCorQRelationLedger.empty.certificateLedger :=
  rfl

/-- The representative imported payload is the typed formal-sum payload plus empty-ledger payload. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
        f F h u).importedRectangleCount +
        TraceCorQRelationLedger.empty.importedRectangleCount :=
  TraceCorQHomRepresentative.importedRectangleCount_eq
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
      f F h u)

/-- The representative bookkeeping payload is the typed formal-sum payload plus empty-ledger payload. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
        f F h u).traceBookkeepingCount +
        TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  TraceCorQHomRepresentative.traceBookkeepingCount_eq
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
      f F h u)

/-- The ambient quotient candidate underlying the scheduled-rectangle channel representative. -/
def completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQQuotientCandidate :=
  (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
    f F h u).rawCandidate

/-- The ambient candidate has the raw scheduled-rectangle channel singleton formal sum. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate_formalSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate
      f F h u).formalSum =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
        f F h u).raw :=
  rfl

/-- The ambient candidate has empty relation ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate_ledger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate
      f F h u).ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- The ambient candidate certificate ledger is the representative certificate ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate
      f F h u).certificateLedger =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
        f F h u).certificateLedger :=
  rfl

/-- The ambient candidate imports the same finite-rectangle payload as the representative. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
        f F h u).importedRectangleCount :=
  rfl

/-- The ambient candidate keeps the same bookkeeping payload as the representative. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
        f F h u).traceBookkeepingCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
