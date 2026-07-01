import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.BoundaryPresentations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Channels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.ReconstructionEquivalence.BulkToBoundary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.ReconstructionEquivalence.BoundaryChannelCompatibility.Owner

/-!
# Reconstruction comparison for trace realization

This owner is for theorems comparing bulk contour data with its boundary and
channel presentations.  Reconstruction belongs after the bulk and realization
layers, so boundary data remains downstream from the bulk category.

Dependency order: bulk-to-boundary presentation, then compatibility between
boundary and channel presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Reconstruction comparison data for trace realization.  It records the
bulk-to-boundary presentation and boundary/channel compatibility surfaces.
-/
structure TraceReconstructionComparison where
  bulkToBoundary : BulkToBoundaryTraceComparison
  boundaryChannel : BoundaryChannelCompatibility
  boundaryChannel_bulkBoundary_eq :
    boundaryChannel.bulkBoundary = bulkToBoundary

namespace TraceReconstructionComparison

/-- The bulk-to-boundary component of trace reconstruction comparison. -/
def bulkBoundary (R : TraceReconstructionComparison) :
    BulkToBoundaryTraceComparison :=
  R.bulkToBoundary

/-- The boundary/channel compatibility component of trace reconstruction comparison. -/
def channelCompatibility (R : TraceReconstructionComparison) :
    BoundaryChannelCompatibility :=
  R.boundaryChannel

/--
The boundary/channel compatibility datum uses the same bulk-to-boundary
comparison as the reconstruction package.
-/
theorem boundaryChannel_bulkBoundary_compatibility
    (R : TraceReconstructionComparison) :
    R.boundaryChannel.bulkBoundary = R.bulkToBoundary :=
  R.boundaryChannel_bulkBoundary_eq

/--
The packet agreement in reconstruction is the packet agreement of the attached
boundary/channel compatibility datum.
-/
theorem packet_eq (R : TraceReconstructionComparison) :
    R.boundaryChannel.bulkBoundary.boundaryPresentation.boundaryStream.packet =
      R.boundaryChannel.channels.vertical.packet :=
  BoundaryChannelCompatibility.packet_eq R.boundaryChannel

end TraceReconstructionComparison

end AnalyticMotives
end LFunctions
end Boundary
