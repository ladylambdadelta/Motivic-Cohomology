import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Constructors.Owner

/-!
# Top-root formal-sum constructor payload projections

This file exposes zero, singleton, and cons constructor payload facts through
the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the zero formal-sum ledger. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_zero_certificateLedger :
    TraceCorQFormalSum.zero.certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQ.formalSum_zero_certificateLedger

/-- The top root exposes the zero formal-sum imported payload count. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_zero_importedRectangleCount :
    TraceCorQFormalSum.zero.importedRectangleCount =
      0 :=
  TraceCorQ.formalSum_zero_importedRectangleCount

/-- The top root exposes the zero formal-sum imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_zero_importedRectangles :
    TraceCorQFormalSum.zero.importedRectangles =
      [] :=
  TraceCorQ.formalSum_zero_importedRectangles

/-- The top root exposes the zero formal-sum bookkeeping payload. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_zero_traceBookkeepingCount :
    TraceCorQFormalSum.zero.traceBookkeepingCount =
      0 :=
  TraceCorQ.formalSum_zero_traceBookkeepingCount

/-- The top root exposes the zero formal-sum rewrite payload. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_zero_rewriteStepCount :
    TraceCorQFormalSum.zero.rewriteStepCount =
      0 :=
  TraceCorQ.formalSum_zero_rewriteStepCount

/-- The top root exposes singleton formal-sum ledgers. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_singleton_certificateLedger
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).certificateLedger =
      ResidueChannelCertificateLedger.append
        generator.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQ.formalSum_singleton_certificateLedger
    coefficient
    generator

/-- The top root exposes singleton formal-sum imported payload counts. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_singleton_importedRectangleCount
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).importedRectangleCount =
      generator.importedRectangleCount +
        ResidueChannelCertificateLedger.empty.importedRectangleCount :=
  TraceCorQ.formalSum_singleton_importedRectangleCount
    coefficient
    generator

/-- The top root exposes singleton formal-sum imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_singleton_importedRectangles
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).importedRectangles =
      generator.importedRectangles ++
        ResidueChannelCertificateLedger.empty.importedRectangles :=
  TraceCorQ.formalSum_singleton_importedRectangles
    coefficient
    generator

/-- The top root exposes singleton formal-sum bookkeeping payloads. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_singleton_traceBookkeepingCount
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).traceBookkeepingCount =
      generator.traceBookkeepingCount +
        ResidueChannelCertificateLedger.empty.traceBookkeepingCount :=
  TraceCorQ.formalSum_singleton_traceBookkeepingCount
    coefficient
    generator

/-- The top root exposes singleton formal-sum rewrite payloads. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_singleton_rewriteStepCount
    (coefficient : Rat) (generator : TraceCorQGenerator) :
    (TraceCorQFormalSum.singleton coefficient generator).rewriteStepCount =
      generator.rewriteStepCount +
        ResidueChannelCertificateLedger.empty.rewriteStepCount :=
  TraceCorQ.formalSum_singleton_rewriteStepCount
    coefficient
    generator

/-- The top root exposes cons formal-sum ledgers. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_cons_certificateLedger
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.certificateLedger (term :: tail) =
      ResidueChannelCertificateLedger.append
        term.certificateLedger
        tail.certificateLedger :=
  TraceCorQ.formalSum_cons_certificateLedger
    term
    tail

/-- The top root exposes cons formal-sum imported payload counts. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_cons_importedRectangleCount
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.importedRectangleCount (term :: tail) =
      term.importedRectangleCount +
        tail.importedRectangleCount :=
  TraceCorQ.formalSum_cons_importedRectangleCount
    term
    tail

/-- The top root exposes cons formal-sum imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_cons_importedRectangles
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.importedRectangles (term :: tail) =
      term.importedRectangles ++
        tail.importedRectangles :=
  TraceCorQ.formalSum_cons_importedRectangles
    term
    tail

/-- The top root exposes cons formal-sum bookkeeping payloads. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_cons_traceBookkeepingCount
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.traceBookkeepingCount (term :: tail) =
      term.traceBookkeepingCount +
        tail.traceBookkeepingCount :=
  TraceCorQ.formalSum_cons_traceBookkeepingCount
    term
    tail

/-- The top root exposes cons formal-sum rewrite payloads. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_cons_rewriteStepCount
    (term : TraceCorQTerm) (tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.rewriteStepCount (term :: tail) =
      term.rewriteStepCount +
        tail.rewriteStepCount :=
  TraceCorQ.formalSum_cons_rewriteStepCount
    term
    tail

end AnalyticMotives
end LFunctions
end Boundary
