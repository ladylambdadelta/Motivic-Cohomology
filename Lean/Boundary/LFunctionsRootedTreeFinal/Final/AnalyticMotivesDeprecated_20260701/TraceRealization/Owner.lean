import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.BoundaryPresentations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Channels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.ReconstructionEquivalence.Owner

/-!
# Trace realization for analytic motives

Trace realization is downstream from bulk analytic contour motives.  It
connects bulk contour data to boundary streams, vertical channels, packet
decompositions, and Hilbert/GNS realizations already exposed in
`TraceCalculus`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Trace realization package for analytic motives.  This is downstream from the
bulk category and packages boundary presentations, channel realizations, and
reconstruction comparison data.
-/
structure AnalyticTraceRealization where
  boundaryPresentation : BoundaryTracePresentation
  channelRealization : TraceChannelRealization
  reconstruction : TraceReconstructionComparison
  boundaryPresentation_eq :
    boundaryPresentation =
      reconstruction.bulkToBoundary.boundaryPresentation
  channelRealization_eq :
    channelRealization =
      reconstruction.boundaryChannel.channels

namespace AnalyticTraceRealization

/-- The boundary-presentation component of trace realization. -/
def boundary (R : AnalyticTraceRealization) :
    BoundaryTracePresentation :=
  R.boundaryPresentation

/-- The channel-realization component of trace realization. -/
def channels (R : AnalyticTraceRealization) :
    TraceChannelRealization :=
  R.channelRealization

/--
The boundary presentation field agrees with the boundary presentation used by
the reconstruction comparison.
-/
theorem boundaryPresentation_compatibility
    (R : AnalyticTraceRealization) :
    R.boundaryPresentation =
      R.reconstruction.bulkToBoundary.boundaryPresentation :=
  R.boundaryPresentation_eq

/--
The channel realization field agrees with the channel realization used by the
reconstruction comparison.
-/
theorem channelRealization_compatibility
    (R : AnalyticTraceRealization) :
    R.channelRealization =
      R.reconstruction.boundaryChannel.channels :=
  R.channelRealization_eq

/--
The packet-comparison realization inside trace realization uses the same
vertical channel as the trace-channel aggregate.
-/
theorem channel_packet_vertical_compatibility
    (R : AnalyticTraceRealization) :
    R.channelRealization.packet.vertical =
      R.channelRealization.vertical :=
  TraceChannelRealization.packet_vertical_compatibility
    R.channelRealization

/--
The archimedean/Binet realization inside trace realization uses the same
packet realization as the trace-channel aggregate.
-/
theorem channel_archimedean_packet_compatibility
    (R : AnalyticTraceRealization) :
    R.channelRealization.archimedean.packetRealization =
      R.channelRealization.packet :=
  TraceChannelRealization.archimedean_packet_compatibility
    R.channelRealization

/--
The archimedean/Binet channel inside trace realization agrees with the
aggregate vertical channel's archimedean component.
-/
theorem channel_archimedeanChannel_compatibility
    (R : AnalyticTraceRealization) :
    R.channelRealization.archimedean.archimedeanChannel =
      R.channelRealization.vertical.archimedeanChannel :=
  TraceChannelRealization.archimedeanChannel_compatibility
    R.channelRealization

/--
The trace realization's vertical channel sum agrees with the owner
trace-calculus vertical channel sum.
-/
theorem channelSum_eq (R : AnalyticTraceRealization) :
    R.channelRealization.vertical.channelSum =
      verticalTraceChannelSum
        R.channelRealization.vertical.packet
        R.channelRealization.vertical.contourFamily
        R.channelRealization.vertical.height :=
  TraceChannelRealization.channelSum_eq R.channelRealization

/--
The trace realization's vertical archimedean channel agrees with the owner
trace-calculus archimedean channel.
-/
theorem archimedean_channel_eq (R : AnalyticTraceRealization) :
    R.channelRealization.vertical.archimedeanChannel =
      archimedeanVerticalTraceChannel
        R.channelRealization.vertical.packet
        R.channelRealization.vertical.contourFamily
        R.channelRealization.vertical.height :=
  TraceChannelRealization.archimedean_channel_eq R.channelRealization

/--
The trace realization's packet boundary-defect Gram agrees with its packet
norm square.
-/
theorem packet_gram_eq_normSq (R : AnalyticTraceRealization) :
    R.channelRealization.packet.boundaryDefectGram =
      R.channelRealization.packet.packetNormSq :=
  TraceChannelRealization.packet_gram_eq_normSq
    R.channelRealization

/--
The trace realization's packet norm square agrees with the owner trace-calculus
packet norm for the aggregate vertical channel.
-/
theorem packet_normSq_eq_owner (R : AnalyticTraceRealization) :
    R.channelRealization.packet.packetNormSq =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        R.channelRealization.vertical.packet 0 :=
  TraceChannelRealization.packet_normSq_eq_owner
    R.channelRealization

/--
The trace realization's packet boundary-defect Gram agrees with the owner
trace-calculus packet norm for the aggregate vertical channel.
-/
theorem packet_gram_eq_owner (R : AnalyticTraceRealization) :
    R.channelRealization.packet.boundaryDefectGram =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        R.channelRealization.vertical.packet 0 :=
  TraceChannelRealization.packet_gram_eq_owner
    R.channelRealization

/--
The boundary presentation and reconstruction comparison are attached to the
same contour-admissible bulk.
-/
theorem boundary_bulk_compatibility
    (R : AnalyticTraceRealization) :
    R.boundaryPresentation.boundaryStream.bulk =
      R.reconstruction.bulkToBoundary.bulk :=
  Eq.trans
    (congrArg
      (fun P =>
        P.boundaryStream.bulk)
      R.boundaryPresentation_eq)
    (BulkToBoundaryTraceComparison.boundary_bulk_eq
      R.reconstruction.bulkToBoundary)

/--
The Hilbert/GNS boundary presentation and the boundary stream presentation in
trace realization are attached to the same contour-admissible bulk.
-/
theorem hilbert_boundary_bulk_compatibility
    (R : AnalyticTraceRealization) :
    R.boundaryPresentation.hilbertSource.boundaryPresentation.bulk =
      R.boundaryPresentation.boundaryStream.bulk :=
  BoundaryTracePresentation.hilbert_bulk_compatibility
    R.boundaryPresentation

/--
The Hilbert/GNS boundary presentation and the boundary stream presentation in
trace realization use the same packet.
-/
theorem hilbert_boundary_packet_compatibility
    (R : AnalyticTraceRealization) :
    R.boundaryPresentation.hilbertSource.boundaryPresentation.packet =
      R.boundaryPresentation.boundaryStream.packet :=
  BoundaryTracePresentation.hilbert_packet_compatibility
    R.boundaryPresentation

/--
The boundary presentation and channel realization in trace realization use the
same packet.
-/
theorem packet_compatibility
    (R : AnalyticTraceRealization) :
    R.boundaryPresentation.boundaryStream.packet =
      R.channelRealization.vertical.packet :=
  Eq.trans
    (congrArg
      (fun P =>
        P.boundaryStream.packet)
      R.boundaryPresentation_eq)
    (Eq.trans
      (congrArg
        (fun C =>
          C.boundaryPresentation.boundaryStream.packet)
        (Eq.symm R.reconstruction.boundaryChannel_bulkBoundary_eq))
      (Eq.trans
        (TraceReconstructionComparison.packet_eq R.reconstruction)
        (congrArg
          (fun C =>
            C.vertical.packet)
          (Eq.symm R.channelRealization_eq))))

end AnalyticTraceRealization

end AnalyticMotives
end LFunctions
end Boundary
