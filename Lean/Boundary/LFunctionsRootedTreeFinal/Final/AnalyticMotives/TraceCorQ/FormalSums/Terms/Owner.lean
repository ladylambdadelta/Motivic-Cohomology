import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Core.Terms.Owner

/-!
# Public weighted-term payload projections

This file exposes the concrete weighted-term certificate and payload
projections under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes weighted-term certificate ledgers. -/
theorem TraceCorQ.term_certificateLedger_eq_generator
    (term : TraceCorQTerm) :
    term.certificateLedger =
      term.2.certificateLedger :=
  TraceCorQTerm.certificateLedger_eq_generator
    term

/-- The trace-correspondence root exposes weighted-term imported payload. -/
theorem TraceCorQ.term_importedRectangleCount_eq_generator
    (term : TraceCorQTerm) :
    term.importedRectangleCount =
      term.2.importedRectangleCount :=
  TraceCorQTerm.importedRectangleCount_eq_generator
    term

/-- The trace-correspondence root exposes weighted-term imported rectangles. -/
theorem TraceCorQ.term_importedRectangles_eq_generator
    (term : TraceCorQTerm) :
    term.importedRectangles =
      term.2.importedRectangles :=
  TraceCorQTerm.importedRectangles_eq_generator
    term

/-- The trace-correspondence root exposes weighted-term imported counts as lengths. -/
theorem TraceCorQ.term_importedRectangleCount_eq_length
    (term : TraceCorQTerm) :
    term.importedRectangleCount =
      term.importedRectangles.length :=
  TraceCorQTerm.importedRectangleCount_eq_length_importedRectangles
    term

/-- The trace-correspondence root exposes weighted-term bookkeeping payload. -/
theorem TraceCorQ.term_traceBookkeepingCount_eq_generator
    (term : TraceCorQTerm) :
    term.traceBookkeepingCount =
      term.2.traceBookkeepingCount :=
  TraceCorQTerm.traceBookkeepingCount_eq_generator
    term

/-- The trace-correspondence root exposes weighted-term rewrite-step payload. -/
theorem TraceCorQ.term_rewriteStepCount_eq_generator
    (term : TraceCorQTerm) :
    term.rewriteStepCount =
      term.2.rewriteStepCount :=
  TraceCorQTerm.rewriteStepCount_eq_generator
    term

end AnalyticMotives
end LFunctions
end Boundary
