import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Core.Basic.Owner

/-!
# Public formal-sum constructor payload projections

This file exposes the concrete zero, singleton, and cons constructor payload
facts under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the zero formal-sum ledger. -/
theorem TraceCorQ.formalSum_zero_certificateLedger :
    TraceCorQFormalSum.zero.certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQFormalSum.zero_certificateLedger

/-- The trace-correspondence root exposes the zero formal-sum imported payload count. -/
theorem TraceCorQ.formalSum_zero_importedRectangleCount :
    TraceCorQFormalSum.zero.importedRectangleCount =
      0 :=
  TraceCorQFormalSum.zero_importedRectangleCount

/-- The trace-correspondence root exposes the zero formal-sum imported rectangles. -/
theorem TraceCorQ.formalSum_zero_importedRectangles :
    TraceCorQFormalSum.zero.importedRectangles =
      [] :=
  TraceCorQFormalSum.zero_importedRectangles

/-- The trace-correspondence root exposes the zero formal-sum bookkeeping payload. -/
theorem TraceCorQ.formalSum_zero_traceBookkeepingCount :
    TraceCorQFormalSum.zero.traceBookkeepingCount =
      0 :=
  TraceCorQFormalSum.zero_traceBookkeepingCount

/-- The trace-correspondence root exposes the zero formal-sum rewrite payload. -/
theorem TraceCorQ.formalSum_zero_rewriteStepCount :
    TraceCorQFormalSum.zero.rewriteStepCount =
      0 :=
  TraceCorQFormalSum.zero_rewriteStepCount

/-- The trace-correspondence root exposes singleton formal-sum ledgers. -/
theorem TraceCorQ.formalSum_singleton_certificateLedger
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).certificateLedger =
      ResidueChannelCertificateLedger.append
        generator.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQFormalSum.singleton_certificateLedger
    coefficient
    generator

/-- The trace-correspondence root exposes singleton formal-sum imported payload counts. -/
theorem TraceCorQ.formalSum_singleton_importedRectangleCount
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).importedRectangleCount =
      generator.importedRectangleCount +
        ResidueChannelCertificateLedger.empty.importedRectangleCount :=
  TraceCorQFormalSum.singleton_importedRectangleCount
    coefficient
    generator

/-- The trace-correspondence root exposes singleton formal-sum imported rectangles. -/
theorem TraceCorQ.formalSum_singleton_importedRectangles
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).importedRectangles =
      generator.importedRectangles ++
        ResidueChannelCertificateLedger.empty.importedRectangles :=
  TraceCorQFormalSum.singleton_importedRectangles
    coefficient
    generator

/-- The trace-correspondence root exposes singleton formal-sum bookkeeping payloads. -/
theorem TraceCorQ.formalSum_singleton_traceBookkeepingCount
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).traceBookkeepingCount =
      generator.traceBookkeepingCount +
        ResidueChannelCertificateLedger.empty.traceBookkeepingCount :=
  TraceCorQFormalSum.singleton_traceBookkeepingCount
    coefficient
    generator

/-- The trace-correspondence root exposes singleton formal-sum rewrite payloads. -/
theorem TraceCorQ.formalSum_singleton_rewriteStepCount
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).rewriteStepCount =
      generator.rewriteStepCount +
        ResidueChannelCertificateLedger.empty.rewriteStepCount :=
  TraceCorQFormalSum.singleton_rewriteStepCount
    coefficient
    generator

/-- The trace-correspondence root exposes cons formal-sum ledgers. -/
theorem TraceCorQ.formalSum_cons_certificateLedger
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.certificateLedger (term :: tail) =
      ResidueChannelCertificateLedger.append
        term.certificateLedger
        tail.certificateLedger :=
  TraceCorQFormalSum.cons_certificateLedger
    term
    tail

/-- The trace-correspondence root exposes cons formal-sum imported payload counts. -/
theorem TraceCorQ.formalSum_cons_importedRectangleCount
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.importedRectangleCount (term :: tail) =
      term.importedRectangleCount +
        tail.importedRectangleCount :=
  TraceCorQFormalSum.cons_importedRectangleCount
    term
    tail

/-- The trace-correspondence root exposes cons formal-sum imported rectangles. -/
theorem TraceCorQ.formalSum_cons_importedRectangles
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.importedRectangles (term :: tail) =
      term.importedRectangles ++
        tail.importedRectangles :=
  TraceCorQFormalSum.cons_importedRectangles
    term
    tail

/-- The trace-correspondence root exposes cons formal-sum bookkeeping payloads. -/
theorem TraceCorQ.formalSum_cons_traceBookkeepingCount
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.traceBookkeepingCount (term :: tail) =
      term.traceBookkeepingCount +
        tail.traceBookkeepingCount :=
  TraceCorQFormalSum.cons_traceBookkeepingCount
    term
    tail

/-- The trace-correspondence root exposes cons formal-sum rewrite payloads. -/
theorem TraceCorQ.formalSum_cons_rewriteStepCount
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.rewriteStepCount (term :: tail) =
      term.rewriteStepCount +
        tail.rewriteStepCount :=
  TraceCorQFormalSum.cons_rewriteStepCount
    term
    tail

end AnalyticMotives
end LFunctions
end Boundary
