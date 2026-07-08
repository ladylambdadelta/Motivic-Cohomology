import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Facade.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Owner

/-!
# Trace-correspondence categorical structures

This file exposes the named category, preadditive, and rational-linear
structures for the trace-correspondence root surface.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the category structure. -/
def traceCorQRootCategory :
    CategoryTheory.Category TraceCorQObject :=
  traceCorQCategory

/-- The trace-correspondence root exposes the preadditive structure. -/
def traceCorQRootPreadditive :
    CategoryTheory.Preadditive TraceCorQObject :=
  traceCorQPreadditive

/-- The trace-correspondence root exposes the rational linear category structure. -/
def traceCorQRootLinearRat :
    CategoryTheory.Linear Rat TraceCorQObject :=
  traceCorQLinearRat

end AnalyticMotives
end LFunctions
end Boundary
