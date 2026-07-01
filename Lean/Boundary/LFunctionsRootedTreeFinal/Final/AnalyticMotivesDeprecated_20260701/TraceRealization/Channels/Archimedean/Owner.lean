import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.ArchimedeanBinet.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Channels.Packet.Owner

/-!
# Archimedean and Binet realization

This file owns the archimedean/Binet normalization surface downstream from
vertical channel and packet realization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Archimedean/Binet realization downstream from packet comparison.  It records
the archimedean vertical channel together with the owner-proved Binet contour
inputs exposed by the trace calculus.
-/
structure ArchimedeanBinetRealization where
  packetRealization : PacketComparisonRealization
  archimedeanChannel : ℂ
  archimedean_eq :
    archimedeanChannel =
      packetRealization.vertical.archimedeanChannel
  branchInput :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption
  endpointInput :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs

namespace ArchimedeanBinetRealization

/-- The archimedean vertical channel in the Binet realization. -/
def channel (A : ArchimedeanBinetRealization) : ℂ :=
  A.archimedeanChannel

end ArchimedeanBinetRealization

end AnalyticMotives
end LFunctions
end Boundary
