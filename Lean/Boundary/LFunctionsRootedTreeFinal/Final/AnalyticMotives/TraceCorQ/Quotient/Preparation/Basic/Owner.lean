import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Core.Owner

/-!
# Basic quotient-input projection facts

This file owns the projection, builder, and empty-input facts for raw
pre-quotient trace-correspondence inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A quotient input certificate ledger is formal-sum certificates followed by relation certificates. -/
theorem TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    (input : TraceCorQQuotientInput) :
    input.certificateLedger =
      ResidueChannelCertificateLedger.append
        input.formalSum.certificateLedger
        input.ledger.certificateLedger :=
  rfl

/-- A quotient input imported payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (input : TraceCorQQuotientInput) :
    input.importedRectangleCount =
      input.formalSum.importedRectangleCount +
        input.ledger.importedRectangleCount :=
  ResidueChannelCertificateLedger.append_importedRectangleCount
    input.formalSum.certificateLedger
    input.ledger.certificateLedger

/-- A quotient input's imported rectangles split into formal-sum and relation-ledger rectangles. -/
theorem TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (input : TraceCorQQuotientInput) :
    input.importedRectangles =
      input.formalSum.importedRectangles ++
        input.ledger.importedRectangles :=
  ResidueChannelCertificateLedger.append_importedRectangles
    input.formalSum.certificateLedger
    input.ledger.certificateLedger

/-- A quotient input's imported-rectangle count is the length of its rectangle list. -/
theorem TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    (input : TraceCorQQuotientInput) :
    input.importedRectangleCount =
      input.importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    input.certificateLedger

/-- A quotient input bookkeeping payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (input : TraceCorQQuotientInput) :
    input.traceBookkeepingCount =
      input.formalSum.traceBookkeepingCount +
        input.ledger.traceBookkeepingCount :=
  ResidueChannelCertificateLedger.append_traceBookkeepingCount
    input.formalSum.certificateLedger
    input.ledger.certificateLedger

/-- A quotient input rewrite-step payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (input : TraceCorQQuotientInput) :
    input.rewriteStepCount =
      input.formalSum.rewriteStepCount +
        input.ledger.rewriteStepCount :=
  ResidueChannelCertificateLedger.append_rewriteStepCount
    input.formalSum.certificateLedger
    input.ledger.certificateLedger

/-- The formal sum projection of a built quotient input. -/
theorem TraceCorQQuotientInput.ofFormalSumLedger_formalSum
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotientInput.ofFormalSumLedger formalSum ledger).formalSum =
      formalSum :=
  rfl

/-- The ledger projection of a built quotient input. -/
theorem TraceCorQQuotientInput.ofFormalSumLedger_ledger
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotientInput.ofFormalSumLedger formalSum ledger).ledger =
      ledger :=
  rfl

/-- The certificate ledger of a built quotient input records formal-sum and relation certificates. -/
theorem TraceCorQQuotientInput.ofFormalSumLedger_certificateLedger
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotientInput.ofFormalSumLedger
      formalSum
      ledger).certificateLedger =
      ResidueChannelCertificateLedger.append
        formalSum.certificateLedger
        ledger.certificateLedger :=
  rfl

/-- Built quotient-input imported payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQQuotientInput.ofFormalSumLedger_importedRectangleCount
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotientInput.ofFormalSumLedger
      formalSum
      ledger).importedRectangleCount =
      formalSum.importedRectangleCount +
        ledger.importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQQuotientInput.ofFormalSumLedger formalSum ledger)

/-- Built quotient-input imported rectangles split into formal-sum and relation-ledger rectangles. -/
theorem TraceCorQQuotientInput.ofFormalSumLedger_importedRectangles
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotientInput.ofFormalSumLedger
      formalSum
      ledger).importedRectangles =
      formalSum.importedRectangles ++
        ledger.importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (TraceCorQQuotientInput.ofFormalSumLedger formalSum ledger)

/-- Built quotient-input bookkeeping payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQQuotientInput.ofFormalSumLedger_traceBookkeepingCount
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotientInput.ofFormalSumLedger
      formalSum
      ledger).traceBookkeepingCount =
      formalSum.traceBookkeepingCount +
        ledger.traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQQuotientInput.ofFormalSumLedger formalSum ledger)

/-- Built quotient-input rewrite-step payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQQuotientInput.ofFormalSumLedger_rewriteStepCount
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotientInput.ofFormalSumLedger
      formalSum
      ledger).rewriteStepCount =
      formalSum.rewriteStepCount +
        ledger.rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQQuotientInput.ofFormalSumLedger formalSum ledger)

/-- The empty quotient input has zero formal sum. -/
theorem TraceCorQQuotientInput.empty_formalSum :
    TraceCorQQuotientInput.empty.formalSum =
      TraceCorQFormalSum.zero :=
  rfl

/-- The empty quotient input has empty relation ledger. -/
theorem TraceCorQQuotientInput.empty_ledger :
    TraceCorQQuotientInput.empty.ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- The empty quotient input carries the empty analytic certificate ledger. -/
theorem TraceCorQQuotientInput.empty_certificateLedger :
    TraceCorQQuotientInput.empty.certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  rfl

/-- The empty quotient input carries no imported finite-rectangle payload. -/
theorem TraceCorQQuotientInput.empty_importedRectangleCount :
    TraceCorQQuotientInput.empty.importedRectangleCount =
      0 :=
  rfl

/-- The empty quotient input exposes no imported finite explicit-formula rectangles. -/
theorem TraceCorQQuotientInput.empty_importedRectangles :
    TraceCorQQuotientInput.empty.importedRectangles =
      [] :=
  rfl

/-- The empty quotient input carries no internal trace-bookkeeping payload. -/
theorem TraceCorQQuotientInput.empty_traceBookkeepingCount :
    TraceCorQQuotientInput.empty.traceBookkeepingCount =
      0 :=
  rfl

/-- The empty quotient input carries no explicit rewrite-step payload. -/
theorem TraceCorQQuotientInput.empty_rewriteStepCount :
    TraceCorQQuotientInput.empty.rewriteStepCount =
      0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
