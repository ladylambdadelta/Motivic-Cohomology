import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Representatives.Owner

/-!
# Payload of typed trace-correspondence composition

This file exposes the certificate-ledger and payload formulas for representative
composition through the composition namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition exposes the representative certificate-ledger formula. -/
theorem TraceCorQComposition.representative_comp_certificateLedger
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQFormalSum.comp left.formalSum.raw right.formalSum.raw).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  TraceCorQHomRepresentative.comp_certificateLedger
    left
    right

/-- Composition exposes the representative imported-rectangle count formula. -/
theorem TraceCorQComposition.representative_comp_importedRectangleCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).importedRectangleCount =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).importedRectangleCount +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  TraceCorQHomRepresentative.comp_importedRectangleCount
    left
    right

/-- Composition exposes the representative imported-rectangle list formula. -/
theorem TraceCorQComposition.representative_comp_importedRectangles
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).importedRectangles =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).importedRectangles ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  TraceCorQHomRepresentative.comp_importedRectangles
    left
    right

/-- Composition exposes the representative trace-bookkeeping count formula. -/
theorem TraceCorQComposition.representative_comp_traceBookkeepingCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).traceBookkeepingCount =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).traceBookkeepingCount +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  TraceCorQHomRepresentative.comp_traceBookkeepingCount
    left
    right

/-- Composition exposes the representative rewrite-step count formula. -/
theorem TraceCorQComposition.representative_comp_rewriteStepCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).rewriteStepCount =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).rewriteStepCount +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  TraceCorQHomRepresentative.comp_rewriteStepCount
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
