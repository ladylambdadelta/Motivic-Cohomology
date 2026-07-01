import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Channels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.ReconstructionEquivalence.BulkToBoundary.Owner

/-!
# Boundary and channel presentation compatibility

This file owns compatibility between boundary trace presentations and channel
realization surfaces.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Compatibility between boundary trace presentation and channel realization.
The compatibility is downstream from both surfaces and compares the packet used
to realize them.
-/
structure BoundaryChannelCompatibility where
  bulkBoundary : BulkToBoundaryTraceComparison
  channels : TraceChannelRealization
  same_packet :
    bulkBoundary.boundaryPresentation.boundaryStream.packet =
      channels.vertical.packet

namespace BoundaryChannelCompatibility

/-- The channel realization in a boundary-channel compatibility datum. -/
def channelData (C : BoundaryChannelCompatibility) :
    TraceChannelRealization :=
  C.channels

/-- The packet agreement between boundary and channel presentations. -/
theorem packet_eq (C : BoundaryChannelCompatibility) :
    C.bulkBoundary.boundaryPresentation.boundaryStream.packet =
      C.channels.vertical.packet :=
  C.same_packet

end BoundaryChannelCompatibility

end AnalyticMotives
end LFunctions
end Boundary
