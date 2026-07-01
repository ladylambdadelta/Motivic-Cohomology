import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.PacketComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Channels.Vertical.Owner

/-!
# Packet comparison realization

This file owns the packet-comparison realization surface downstream from
vertical channel realization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Packet comparison realization downstream from vertical channels.  It records
the boundary-defect Gram and packet norm surface exposed by the trace calculus.
-/
structure PacketComparisonRealization where
  vertical : VerticalChannelRealization
  boundaryDefectGram : ℝ
  packetNormSq : ℝ
  gram_eq_packet :
    boundaryDefectGram = packetNormSq
  packet_eq_owner :
    packetNormSq =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        vertical.packet 0

namespace PacketComparisonRealization

/-- The packet norm square in the realization. -/
def normSq (P : PacketComparisonRealization) : ℝ :=
  P.packetNormSq

/-- The boundary-defect Gram agrees with the packet norm square. -/
theorem gram_eq_normSq (P : PacketComparisonRealization) :
    P.boundaryDefectGram = P.packetNormSq :=
  P.gram_eq_packet

/-- The packet norm square agrees with the owner trace-calculus packet norm. -/
theorem normSq_eq_owner (P : PacketComparisonRealization) :
    P.packetNormSq =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        P.vertical.packet 0 :=
  P.packet_eq_owner

/-- The boundary-defect Gram agrees with the owner trace-calculus packet norm. -/
theorem gram_eq_owner (P : PacketComparisonRealization) :
    P.boundaryDefectGram =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        P.vertical.packet 0 :=
  Eq.trans P.gram_eq_packet P.packet_eq_owner

end PacketComparisonRealization

end AnalyticMotives
end LFunctions
end Boundary
