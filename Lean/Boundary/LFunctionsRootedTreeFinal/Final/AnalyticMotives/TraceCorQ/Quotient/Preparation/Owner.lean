import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Basic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Add.Owner

/-!
# Quotient preparation for Q-linear trace correspondences

This file owns the raw input package consumed by the quotient relation.

A quotient input is a formal Q-linear trace-correspondence sum together with
the finite relation ledger available to reduce it.  This facade records scalar
and composition payload facts not owned by the basic or additive subfiles.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The formal sum of a scaled quotient input is the scaled formal sum. -/
theorem TraceCorQQuotientInput.smul_formalSum
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.smul coefficient input).formalSum =
      TraceCorQFormalSum.smul coefficient input.formalSum :=
  rfl

/-- Scaling a quotient input preserves its relation ledger. -/
theorem TraceCorQQuotientInput.smul_ledger
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.smul coefficient input).ledger =
      input.ledger :=
  rfl

/-- Scaling a quotient input preserves its analytic certificate ledger. -/
theorem TraceCorQQuotientInput.smul_certificateLedger
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.smul coefficient input).certificateLedger =
      input.certificateLedger :=
  congrArg
    (fun formalSumCertificateLedger =>
      ResidueChannelCertificateLedger.append
        formalSumCertificateLedger
        input.ledger.certificateLedger)
    (TraceCorQFormalSum.smul_certificateLedger
      coefficient
      input.formalSum)

/-- Scaling a quotient input preserves imported finite-rectangle payload. -/
theorem TraceCorQQuotientInput.smul_importedRectangleCount
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.smul coefficient input).importedRectangleCount =
      input.importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceCorQQuotientInput.smul_certificateLedger coefficient input)

/-- Scaling a quotient input preserves imported finite explicit-formula rectangles. -/
theorem TraceCorQQuotientInput.smul_importedRectangles
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.smul coefficient input).importedRectangles =
      input.importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceCorQQuotientInput.smul_certificateLedger coefficient input)

/-- Scaling a quotient input preserves internal trace-bookkeeping payload. -/
theorem TraceCorQQuotientInput.smul_traceBookkeepingCount
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.smul coefficient input).traceBookkeepingCount =
      input.traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceCorQQuotientInput.smul_certificateLedger coefficient input)

/-- Scaling a quotient input preserves explicit rewrite-step payload. -/
theorem TraceCorQQuotientInput.smul_rewriteStepCount
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.smul coefficient input).rewriteStepCount =
      input.rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceCorQQuotientInput.smul_certificateLedger coefficient input)

/-- The formal sum of a quotient-input composition is the composed formal sum. -/
theorem TraceCorQQuotientInput.comp_formalSum
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp left right).formalSum =
      TraceCorQFormalSum.comp left.formalSum right.formalSum :=
  rfl

/-- The ledger of a quotient-input composition is the appended ledger. -/
theorem TraceCorQQuotientInput.comp_ledger
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  rfl

/-- The certificate ledger of quotient-input composition records composed formal and relation certificates. -/
theorem TraceCorQQuotientInput.comp_certificateLedger
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQFormalSum.comp left.formalSum right.formalSum).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  congrArg
    (ResidueChannelCertificateLedger.append
      (TraceCorQFormalSum.comp left.formalSum right.formalSum).certificateLedger)
    (TraceCorQRelationLedger.append_certificateLedger
      left.ledger
      right.ledger)

/-- Quotient-input composition splits imported payload into composed formal and relation parts. -/
theorem TraceCorQQuotientInput.comp_importedRectangleCount
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp left right).importedRectangleCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).importedRectangleCount +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangleCount
        (TraceCorQQuotientInput.comp_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        (TraceCorQFormalSum.comp
          left.formalSum
          right.formalSum).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg
      (fun count =>
        (TraceCorQFormalSum.comp
          left.formalSum
          right.formalSum).importedRectangleCount +
          count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Quotient-input composition splits imported rectangles into composed formal and relation parts. -/
theorem TraceCorQQuotientInput.comp_importedRectangles
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp left right).importedRectangles =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).importedRectangles ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangles
        (TraceCorQQuotientInput.comp_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_importedRectangles
        (TraceCorQFormalSum.comp
          left.formalSum
          right.formalSum).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg
      (fun rectangles =>
        (TraceCorQFormalSum.comp
          left.formalSum
          right.formalSum).importedRectangles ++
          rectangles)
      (ResidueChannelCertificateLedger.append_importedRectangles
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Quotient-input composition splits bookkeeping payload into composed formal and relation parts. -/
theorem TraceCorQQuotientInput.comp_traceBookkeepingCount
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp left right).traceBookkeepingCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).traceBookkeepingCount +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.traceBookkeepingCount
        (TraceCorQQuotientInput.comp_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        (TraceCorQFormalSum.comp
          left.formalSum
          right.formalSum).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg
      (fun count =>
        (TraceCorQFormalSum.comp
          left.formalSum
          right.formalSum).traceBookkeepingCount +
          count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Quotient-input composition splits rewrite-step payload into composed formal and relation parts. -/
theorem TraceCorQQuotientInput.comp_rewriteStepCount
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp left right).rewriteStepCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).rewriteStepCount +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.rewriteStepCount
        (TraceCorQQuotientInput.comp_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        (TraceCorQFormalSum.comp
          left.formalSum
          right.formalSum).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg
      (fun count =>
        (TraceCorQFormalSum.comp
          left.formalSum
          right.formalSum).rewriteStepCount +
          count)
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Composition with the empty input on the right exposes only the left relation ledger payload. -/
theorem TraceCorQQuotientInput.comp_empty_rewriteStepCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      input
      TraceCorQQuotientInput.empty).rewriteStepCount =
      0 +
        (input.ledger.rewriteStepCount +
          TraceCorQRelationLedger.empty.rewriteStepCount) :=
  Eq.trans
    (TraceCorQQuotientInput.comp_rewriteStepCount
      input
      TraceCorQQuotientInput.empty)
    (congrArg
      (fun count =>
        count +
          (input.ledger.rewriteStepCount +
            TraceCorQRelationLedger.empty.rewriteStepCount))
      (TraceCorQFormalSum.comp_zero_rewriteStepCount input.formalSum))

end AnalyticMotives
end LFunctions
end Boundary
