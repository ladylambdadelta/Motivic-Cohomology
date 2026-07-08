import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Facade.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Facade.Structures.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Category.Owner

/-!
# Top-root trace-correspondence structures

This file exposes the trace-correspondence category, preadditive, and
rational-linear structures under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the trace-correspondence category structure. -/
def AnalyticMotivesRoot.traceCorQCategory :
    CategoryTheory.Category TraceCorQObject :=
  traceCorQRootCategory

/-- The top root exposes the trace-correspondence preadditive structure. -/
def AnalyticMotivesRoot.traceCorQPreadditive :
    CategoryTheory.Preadditive TraceCorQObject :=
  traceCorQRootPreadditive

/-- The top root exposes the rational linear trace-correspondence structure. -/
def AnalyticMotivesRoot.traceCorQLinearRat :
    CategoryTheory.Linear Rat TraceCorQObject :=
  traceCorQRootLinearRat

end AnalyticMotives
end LFunctions
end Boundary
