import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.VerticalChannels.Owner

/-!
# Vertical channel realization

This file owns the trace-realization surface to prime, archimedean,
correction, and inverse-Gamma vertical channels.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Vertical channel realization attached to bulk analytic contour data and an
admissible trace packet.
-/
structure VerticalChannelRealization where
  bulk : ContourAdmissibleBulk
  packet : ZetaAdmissibleFunction
  contourFamily : TraceContourFamily
  height : ℝ
  primeChannel : ℂ
  archimedeanChannel : ℂ
  correctionChannel : ℂ
  inverseGammaChannel : ℂ
  channelSum : ℂ
  prime_eq :
    primeChannel =
      primeVerticalTraceChannel packet contourFamily height
  archimedean_eq :
    archimedeanChannel =
      archimedeanVerticalTraceChannel packet contourFamily height
  correction_eq :
    correctionChannel =
      correctionVerticalTraceChannel packet contourFamily height
  inverseGamma_eq :
    inverseGammaChannel =
      inverseGammaCompletionVerticalTraceChannel packet contourFamily height
  sum_eq :
    channelSum =
      verticalTraceChannelSum packet contourFamily height

namespace VerticalChannelRealization

/-- The realized finite-height vertical channel sum. -/
def sum (V : VerticalChannelRealization) : ℂ :=
  V.channelSum

/-- The prime channel agrees with the owner trace-calculus prime channel. -/
theorem prime_channel_eq (V : VerticalChannelRealization) :
    V.primeChannel =
      primeVerticalTraceChannel V.packet V.contourFamily V.height :=
  V.prime_eq

/-- The archimedean channel agrees with the owner trace-calculus archimedean channel. -/
theorem archimedean_channel_eq (V : VerticalChannelRealization) :
    V.archimedeanChannel =
      archimedeanVerticalTraceChannel V.packet V.contourFamily V.height :=
  V.archimedean_eq

/-- The correction channel agrees with the owner trace-calculus correction channel. -/
theorem correction_channel_eq (V : VerticalChannelRealization) :
    V.correctionChannel =
      correctionVerticalTraceChannel V.packet V.contourFamily V.height :=
  V.correction_eq

/--
The inverse-Gamma channel agrees with the owner trace-calculus inverse-Gamma
completion channel.
-/
theorem inverseGamma_channel_eq (V : VerticalChannelRealization) :
    V.inverseGammaChannel =
      inverseGammaCompletionVerticalTraceChannel
        V.packet V.contourFamily V.height :=
  V.inverseGamma_eq

/-- The channel sum agrees with the owner trace-calculus vertical channel sum. -/
theorem channelSum_eq (V : VerticalChannelRealization) :
    V.channelSum =
      verticalTraceChannelSum V.packet V.contourFamily V.height :=
  V.sum_eq

end VerticalChannelRealization

end AnalyticMotives
end LFunctions
end Boundary
