import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Terms.Owner

/-!
# Top-root weighted-term payload projections

This file exposes weighted trace-correspondence term payload projections
through the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes weighted-term certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQTerm_certificateLedger_eq_generator
    (term : TraceCorQTerm) :
    term.certificateLedger =
      term.2.certificateLedger :=
  TraceCorQ.term_certificateLedger_eq_generator
    term

/-- The top root exposes weighted-term imported payload. -/
theorem AnalyticMotivesRoot.traceCorQTerm_importedRectangleCount_eq_generator
    (term : TraceCorQTerm) :
    term.importedRectangleCount =
      term.2.importedRectangleCount :=
  TraceCorQ.term_importedRectangleCount_eq_generator
    term

/-- The top root exposes weighted-term imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQTerm_importedRectangles_eq_generator
    (term : TraceCorQTerm) :
    term.importedRectangles =
      term.2.importedRectangles :=
  TraceCorQ.term_importedRectangles_eq_generator
    term

/-- The top root exposes weighted-term imported counts as lengths. -/
theorem AnalyticMotivesRoot.traceCorQTerm_importedRectangleCount_eq_length
    (term : TraceCorQTerm) :
    term.importedRectangleCount =
      term.importedRectangles.length :=
  TraceCorQ.term_importedRectangleCount_eq_length
    term

/-- The top root exposes weighted-term bookkeeping payload. -/
theorem AnalyticMotivesRoot.traceCorQTerm_traceBookkeepingCount_eq_generator
    (term : TraceCorQTerm) :
    term.traceBookkeepingCount =
      term.2.traceBookkeepingCount :=
  TraceCorQ.term_traceBookkeepingCount_eq_generator
    term

/-- The top root exposes weighted-term rewrite-step payload. -/
theorem AnalyticMotivesRoot.traceCorQTerm_rewriteStepCount_eq_generator
    (term : TraceCorQTerm) :
    term.rewriteStepCount =
      term.2.rewriteStepCount :=
  TraceCorQ.term_rewriteStepCount_eq_generator
    term

end AnalyticMotives
end LFunctions
end Boundary
