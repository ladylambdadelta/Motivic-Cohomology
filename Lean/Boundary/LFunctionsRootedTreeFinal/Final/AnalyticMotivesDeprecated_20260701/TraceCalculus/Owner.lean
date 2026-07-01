import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.BoundaryStream.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.HilbertRealization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.PacketComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.ArchimedeanBinet.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.VerticalChannels.Owner

/-!
# Analytic-motive trace calculus

This owner surface collects high-level wrappers around the existing completed
boundary stream, Hilbert/GNS, packet comparison, Binet contour, and vertical
channel APIs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Aggregate trace-calculus package for a zeta test packet and finite-height
contour family.  This is a downstream realization surface: it collects the
already-owned boundary stream, Hilbert/GNS, packet comparison, Binet, and
vertical-channel APIs under one analytic-motive-facing object.
-/
structure AnalyticTraceCalculusPackage where
  packet : ZetaAdmissibleFunction
  contourFamily : TraceContourFamily
  height : ℝ
  boundaryStream : BoundaryTraceStream
  hilbertSource : BoundaryHilbertSource
  primeChannel : ℂ
  archimedeanChannel : ℂ
  correctionChannel : ℂ
  inverseGammaCompletionChannel : ℂ
  verticalChannelSum : ℂ
  boundaryDefectGram : ℝ
  packetNormSq : ℝ
  gnsNormSq : ℝ
  binetBranchInput :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption
  binetEndpointInput :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs

namespace AnalyticTraceCalculusPackage

/-- The canonical trace-calculus package attached to a packet, contour family, and height. -/
def canonical
    (f : ZetaAdmissibleFunction) (F : TraceContourFamily) (T : ℝ) :
    AnalyticTraceCalculusPackage where
  packet := f
  contourFamily := F
  height := T
  boundaryStream := boundaryTraceStream f
  hilbertSource := boundaryHilbertSource f
  primeChannel := primeVerticalTraceChannel f F T
  archimedeanChannel := archimedeanVerticalTraceChannel f F T
  correctionChannel := correctionVerticalTraceChannel f F T
  inverseGammaCompletionChannel :=
    inverseGammaCompletionVerticalTraceChannel f F T
  verticalChannelSum := verticalTraceChannelSum f F T
  boundaryDefectGram :=
    ZetaAdmissibleFunction.zetaCompletedBoundaryDefectGram f
  packetNormSq :=
    ZetaAdmissibleFunction.zetaCompletedPacketNormSq f 0
  gnsNormSq := boundaryRealShadowGNSNormSq f
  binetBranchInput := binetBranchUniformTailAbsorption
  binetEndpointInput := binetEndpointRestoredFiniteHeightContourInputs

/-- The boundary trace stream in an aggregate trace-calculus package. -/
def stream (P : AnalyticTraceCalculusPackage) :
    BoundaryTraceStream :=
  P.boundaryStream

/-- The Hilbert/GNS source in an aggregate trace-calculus package. -/
def hilbert (P : AnalyticTraceCalculusPackage) :
    BoundaryHilbertSource :=
  P.hilbertSource

/-- The completed boundary-defect Gram in an aggregate trace-calculus package. -/
def gram (P : AnalyticTraceCalculusPackage) : ℝ :=
  P.boundaryDefectGram

/-- The packet norm square in an aggregate trace-calculus package. -/
def normSq (P : AnalyticTraceCalculusPackage) : ℝ :=
  P.packetNormSq

/-- The finite-height vertical channel sum in an aggregate trace-calculus package. -/
def channelSum (P : AnalyticTraceCalculusPackage) : ℂ :=
  P.verticalChannelSum

/-- The archimedean Binet branch input in an aggregate trace-calculus package. -/
def binetBranch
    (P : AnalyticTraceCalculusPackage) :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
  P.binetBranchInput

/-- The archimedean Binet endpoint input in an aggregate trace-calculus package. -/
def binetEndpoint
    (P : AnalyticTraceCalculusPackage) :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs :=
  P.binetEndpointInput

end AnalyticTraceCalculusPackage

end AnalyticMotives
end LFunctions
end Boundary
