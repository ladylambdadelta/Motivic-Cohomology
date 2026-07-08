import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Core.Owner

/-!
# Addition facts for quotient preparation inputs

This file owns the projection and payload facts for addition of raw quotient
inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The formal sum of a quotient-input sum is the sum of formal sums. -/
theorem TraceCorQQuotientInput.add_formalSum
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.add left right).formalSum =
      TraceCorQFormalSum.add left.formalSum right.formalSum :=
  rfl

/-- The ledger of a quotient-input sum is the appended ledger. -/
theorem TraceCorQQuotientInput.add_ledger
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.add left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  rfl

/-- The certificate ledger of a quotient-input sum records summed formal and relation certificates. -/
theorem TraceCorQQuotientInput.add_certificateLedger
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.add left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  congrArg₂
    ResidueChannelCertificateLedger.append
    (TraceCorQFormalSum.add_certificateLedger
      left.formalSum
      right.formalSum)
    (TraceCorQRelationLedger.append_certificateLedger
      left.ledger
      right.ledger)

/-- Quotient-input addition adds imported finite-rectangle payload by component. -/
theorem TraceCorQQuotientInput.add_importedRectangleCount
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.add left right).importedRectangleCount =
      (left.formalSum.importedRectangleCount +
        right.formalSum.importedRectangleCount) +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangleCount
        (TraceCorQQuotientInput.add_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg₂
      Nat.add
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        left.formalSum.certificateLedger
        right.formalSum.certificateLedger)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Quotient-input addition concatenates imported rectangle payload by component. -/
theorem TraceCorQQuotientInput.add_importedRectangles
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.add left right).importedRectangles =
      (left.formalSum.importedRectangles ++
        right.formalSum.importedRectangles) ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangles
        (TraceCorQQuotientInput.add_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_importedRectangles
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg₂
      List.append
      (ResidueChannelCertificateLedger.append_importedRectangles
        left.formalSum.certificateLedger
        right.formalSum.certificateLedger)
      (ResidueChannelCertificateLedger.append_importedRectangles
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Quotient-input addition adds internal trace-bookkeeping payload by component. -/
theorem TraceCorQQuotientInput.add_traceBookkeepingCount
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.add left right).traceBookkeepingCount =
      (left.formalSum.traceBookkeepingCount +
        right.formalSum.traceBookkeepingCount) +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.traceBookkeepingCount
        (TraceCorQQuotientInput.add_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg₂
      Nat.add
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        left.formalSum.certificateLedger
        right.formalSum.certificateLedger)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Quotient-input addition adds explicit rewrite-step payload by component. -/
theorem TraceCorQQuotientInput.add_rewriteStepCount
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.add left right).rewriteStepCount =
      (left.formalSum.rewriteStepCount +
        right.formalSum.rewriteStepCount) +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.rewriteStepCount
        (TraceCorQQuotientInput.add_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg₂
      Nat.add
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        left.formalSum.certificateLedger
        right.formalSum.certificateLedger)
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

end AnalyticMotives
end LFunctions
end Boundary
