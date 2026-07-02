import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectangleHom.Owner

/-!
# Zero-pole rectangle-certified representatives

This file records the explicit pre-quotient representative and ambient quotient
candidate underlying the rectangle-certified zero-pole residue hom.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The explicit representative of the rectangle-certified zero-pole residue hom. -/
def completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative
    (R : ℝ) :
    TraceCorQHomRepresentative
      (completedZetaZeroPoleResidueRectangleHomSource R)
      completedZetaZeroPoleResidueRectangleHomTarget :=
  TraceCorQHomRepresentative.ofFormalSumLedger
    (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R)
    TraceCorQRelationLedger.empty

/-- The rectangle-certified representative has the singleton typed formal sum. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative_formalSum
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).formalSum =
      completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R :=
  rfl

/-- The rectangle-certified representative has empty relation ledger. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative_ledger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- The rectangle-certified representative records formal-sum certificates and the empty ledger. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).certificateLedger =
      ResidueChannelCertificateLedger.append
        (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).certificateLedger
        TraceCorQRelationLedger.empty.certificateLedger :=
  rfl

/-- The representative imported payload is the typed formal-sum payload plus empty-ledger payload. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).importedRectangleCount +
        TraceCorQRelationLedger.empty.importedRectangleCount :=
  TraceCorQHomRepresentative.importedRectangleCount_eq
    (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R)

/-- The representative bookkeeping payload is the typed formal-sum payload plus empty-ledger payload. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).traceBookkeepingCount +
        TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  TraceCorQHomRepresentative.traceBookkeepingCount_eq
    (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R)

/-- The ambient quotient candidate underlying the rectangle-certified representative. -/
def completedZetaZeroPoleResidueRectangleTraceCorQCandidate
    (R : ℝ) :
    TraceCorQQuotientCandidate :=
  (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).rawCandidate

/-- The ambient candidate has the raw rectangle-certified singleton formal sum. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQCandidate_formalSum
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQCandidate R).formalSum =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).raw :=
  rfl

/-- The ambient candidate has empty relation ledger. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQCandidate_ledger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQCandidate R).ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- The ambient candidate certificate ledger is the representative certificate ledger. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQCandidate_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleTraceCorQCandidate R).certificateLedger =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).certificateLedger :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
