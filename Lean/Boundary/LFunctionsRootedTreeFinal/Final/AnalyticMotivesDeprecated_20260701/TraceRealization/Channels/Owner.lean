import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.VerticalChannels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.PacketComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.ArchimedeanBinet.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Channels.Vertical.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Channels.Packet.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Channels.Archimedean.Owner

/-!
# Channel realization of analytic motives

This file owns the realization path from bulk contour data to the explicit
prime, archimedean, correction, inverse-Gamma, packet, and Binet channel
surfaces already exposed in `TraceCalculus`.

Dependency order: vertical channels, packet comparison, then archimedean/Binet
normalization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Trace-channel realization of analytic motives: vertical channels, packet
comparison, and archimedean/Binet normalization as downstream surfaces.
-/
structure TraceChannelRealization where
  vertical : VerticalChannelRealization
  packet : PacketComparisonRealization
  archimedean : ArchimedeanBinetRealization
  packet_vertical_eq :
    packet.vertical = vertical
  archimedean_packet_eq :
    archimedean.packetRealization = packet

namespace TraceChannelRealization

/-- The vertical-channel component of trace-channel realization. -/
def verticalData (R : TraceChannelRealization) :
    VerticalChannelRealization :=
  R.vertical

/-- The packet-comparison component of trace-channel realization. -/
def packetData (R : TraceChannelRealization) :
    PacketComparisonRealization :=
  R.packet

/-- The packet-comparison realization uses the aggregate vertical channel. -/
theorem packet_vertical_compatibility
    (R : TraceChannelRealization) :
    R.packet.vertical = R.vertical :=
  R.packet_vertical_eq

/-- The archimedean/Binet realization uses the aggregate packet realization. -/
theorem archimedean_packet_compatibility
    (R : TraceChannelRealization) :
    R.archimedean.packetRealization = R.packet :=
  R.archimedean_packet_eq

/--
The archimedean/Binet realization uses the aggregate vertical channel after
passing through its packet realization.
-/
theorem archimedean_vertical_compatibility
    (R : TraceChannelRealization) :
    R.archimedean.packetRealization.vertical = R.vertical :=
  Eq.trans
    (congrArg PacketComparisonRealization.vertical
      R.archimedean_packet_eq)
    R.packet_vertical_eq

/--
The archimedean channel in the aggregate Binet realization agrees with the
aggregate vertical channel's archimedean component.
-/
theorem archimedeanChannel_compatibility
    (R : TraceChannelRealization) :
    R.archimedean.archimedeanChannel =
      R.vertical.archimedeanChannel :=
  Eq.trans R.archimedean.archimedean_eq
    (congrArg VerticalChannelRealization.archimedeanChannel
      (archimedean_vertical_compatibility R))

/-- The aggregate prime channel agrees with the owner trace-calculus prime channel. -/
theorem prime_channel_eq (R : TraceChannelRealization) :
    R.vertical.primeChannel =
      primeVerticalTraceChannel
        R.vertical.packet R.vertical.contourFamily R.vertical.height :=
  VerticalChannelRealization.prime_channel_eq R.vertical

/--
The aggregate archimedean channel agrees with the owner trace-calculus
archimedean channel.
-/
theorem archimedean_channel_eq (R : TraceChannelRealization) :
    R.vertical.archimedeanChannel =
      archimedeanVerticalTraceChannel
        R.vertical.packet R.vertical.contourFamily R.vertical.height :=
  VerticalChannelRealization.archimedean_channel_eq R.vertical

/-- The aggregate correction channel agrees with the owner trace-calculus correction channel. -/
theorem correction_channel_eq (R : TraceChannelRealization) :
    R.vertical.correctionChannel =
      correctionVerticalTraceChannel
        R.vertical.packet R.vertical.contourFamily R.vertical.height :=
  VerticalChannelRealization.correction_channel_eq R.vertical

/--
The aggregate inverse-Gamma channel agrees with the owner trace-calculus
inverse-Gamma completion channel.
-/
theorem inverseGamma_channel_eq (R : TraceChannelRealization) :
    R.vertical.inverseGammaChannel =
      inverseGammaCompletionVerticalTraceChannel
        R.vertical.packet R.vertical.contourFamily R.vertical.height :=
  VerticalChannelRealization.inverseGamma_channel_eq R.vertical

/-- The aggregate channel sum agrees with the owner trace-calculus vertical channel sum. -/
theorem channelSum_eq (R : TraceChannelRealization) :
    R.vertical.channelSum =
      verticalTraceChannelSum
        R.vertical.packet R.vertical.contourFamily R.vertical.height :=
  VerticalChannelRealization.channelSum_eq R.vertical

/-- The aggregate packet boundary-defect Gram agrees with its packet norm square. -/
theorem packet_gram_eq_normSq (R : TraceChannelRealization) :
    R.packet.boundaryDefectGram = R.packet.packetNormSq :=
  PacketComparisonRealization.gram_eq_normSq R.packet

/--
The aggregate packet norm square agrees with the owner trace-calculus packet
norm for the aggregate vertical channel.
-/
theorem packet_normSq_eq_owner (R : TraceChannelRealization) :
    R.packet.packetNormSq =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        R.vertical.packet 0 :=
  Eq.trans
    (PacketComparisonRealization.normSq_eq_owner R.packet)
    (congrArg
      (fun V =>
        ZetaAdmissibleFunction.zetaCompletedPacketNormSq
          V.packet 0)
      R.packet_vertical_eq)

/--
The aggregate packet boundary-defect Gram agrees with the owner trace-calculus
packet norm for the aggregate vertical channel.
-/
theorem packet_gram_eq_owner (R : TraceChannelRealization) :
    R.packet.boundaryDefectGram =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        R.vertical.packet 0 :=
  Eq.trans
    (PacketComparisonRealization.gram_eq_owner R.packet)
    (congrArg
      (fun V =>
        ZetaAdmissibleFunction.zetaCompletedPacketNormSq
          V.packet 0)
      R.packet_vertical_eq)

end TraceChannelRealization

end AnalyticMotives
end LFunctions
end Boundary
