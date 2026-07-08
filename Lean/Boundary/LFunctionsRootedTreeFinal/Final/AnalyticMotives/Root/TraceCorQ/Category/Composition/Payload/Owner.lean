import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Payload.Owner

/-!
# Public payload of typed trace-correspondence composition

This file exposes representative composition payload formulas through the
public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: representative composition certificate-ledger formula. -/
theorem AnalyticMotivesRoot.traceCorQRepresentative_comp_certificateLedger
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQFormalSum.comp left.formalSum.raw right.formalSum.raw).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  TraceCorQComposition.representative_comp_certificateLedger
    left
    right

/-- Public wrapper: representative composition imported-rectangle count formula. -/
theorem AnalyticMotivesRoot.traceCorQRepresentative_comp_importedRectangleCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).importedRectangleCount =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).importedRectangleCount +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  TraceCorQComposition.representative_comp_importedRectangleCount
    left
    right

/-- Public wrapper: representative composition imported-rectangle list formula. -/
theorem AnalyticMotivesRoot.traceCorQRepresentative_comp_importedRectangles
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).importedRectangles =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).importedRectangles ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  TraceCorQComposition.representative_comp_importedRectangles
    left
    right

/-- Public wrapper: representative composition trace-bookkeeping count formula. -/
theorem AnalyticMotivesRoot.traceCorQRepresentative_comp_traceBookkeepingCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).traceBookkeepingCount =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).traceBookkeepingCount +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  TraceCorQComposition.representative_comp_traceBookkeepingCount
    left
    right

/-- Public wrapper: representative composition rewrite-step count formula. -/
theorem AnalyticMotivesRoot.traceCorQRepresentative_comp_rewriteStepCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).rewriteStepCount =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).rewriteStepCount +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  TraceCorQComposition.representative_comp_rewriteStepCount
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
