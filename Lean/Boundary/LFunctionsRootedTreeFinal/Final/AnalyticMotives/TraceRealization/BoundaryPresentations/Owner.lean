import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.BoundaryStream.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.HilbertRealization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.BoundaryPresentations.BoundaryStream.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.BoundaryPresentations.HilbertSource.Owner

/-!
# Boundary presentations of trace realization

This file owns the realization path from bulk analytic contour data to boundary
trace streams and Hilbert/GNS sources.  Boundary presentations are realization
surfaces attached to analytic motives.

Dependency order: boundary stream presentation, then Hilbert/GNS presentation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Boundary presentation data for trace realization: a boundary stream together
with its Hilbert/GNS presentation.
-/
structure BoundaryTracePresentation where
  boundaryStream : BoundaryStreamPresentation
  hilbertSource : HilbertSourcePresentation
  hilbert_boundaryPresentation_eq :
    hilbertSource.boundaryPresentation = boundaryStream

namespace BoundaryTracePresentation

/-- The boundary-stream part of a boundary trace presentation. -/
def streamPresentation (P : BoundaryTracePresentation) :
    BoundaryStreamPresentation :=
  P.boundaryStream

/-- The Hilbert/GNS part of a boundary trace presentation. -/
def hilbertPresentation (P : BoundaryTracePresentation) :
    HilbertSourcePresentation :=
  P.hilbertSource

/--
The Hilbert/GNS presentation uses the same boundary-stream presentation as the
boundary trace presentation package.
-/
theorem hilbert_boundaryPresentation_compatibility
    (P : BoundaryTracePresentation) :
    P.hilbertSource.boundaryPresentation = P.boundaryStream :=
  P.hilbert_boundaryPresentation_eq

/--
The Hilbert/GNS presentation and boundary stream presentation are attached to
the same contour-admissible bulk.
-/
theorem hilbert_bulk_compatibility
    (P : BoundaryTracePresentation) :
    P.hilbertSource.boundaryPresentation.bulk =
      P.boundaryStream.bulk :=
  congrArg BoundaryStreamPresentation.bulk
    P.hilbert_boundaryPresentation_eq

/--
The Hilbert/GNS presentation and boundary stream presentation use the same
packet.
-/
theorem hilbert_packet_compatibility
    (P : BoundaryTracePresentation) :
    P.hilbertSource.boundaryPresentation.packet =
      P.boundaryStream.packet :=
  congrArg BoundaryStreamPresentation.packet
    P.hilbert_boundaryPresentation_eq

end BoundaryTracePresentation

end AnalyticMotives
end LFunctions
end Boundary
