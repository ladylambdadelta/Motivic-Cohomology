import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.BoundaryStream.Owner

/-!
# Boundary stream presentation

This file owns the trace-realization surface from bulk analytic contour data to
completed boundary trace streams.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Boundary-stream presentation of an analytic motive.  This is a downstream
trace-realization surface: it attaches an already-owned boundary trace stream
to bulk analytic contour data.
-/
structure BoundaryStreamPresentation where
  bulk : ContourAdmissibleBulk
  packet : ZetaAdmissibleFunction
  stream : BoundaryTraceStream
  stream_eq : stream = boundaryTraceStream packet

namespace BoundaryStreamPresentation

/-- The realized boundary trace stream. -/
def realizedStream (P : BoundaryStreamPresentation) : BoundaryTraceStream :=
  P.stream

/-- The canonical identification with the exposed trace-calculus stream. -/
theorem realizedStream_eq (P : BoundaryStreamPresentation) :
    P.stream = boundaryTraceStream P.packet :=
  P.stream_eq

end BoundaryStreamPresentation

end AnalyticMotives
end LFunctions
end Boundary
