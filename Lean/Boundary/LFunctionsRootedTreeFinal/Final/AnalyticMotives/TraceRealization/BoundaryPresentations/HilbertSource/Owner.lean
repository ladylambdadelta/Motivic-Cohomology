import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.HilbertRealization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.BoundaryPresentations.BoundaryStream.Owner

/-!
# Hilbert/GNS presentation

This file owns the Hilbert/GNS trace-realization surface downstream from the
boundary stream presentation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Hilbert/GNS presentation downstream from a boundary-stream presentation.  It
attaches the already-owned completed boundary Hilbert source and GNS scalar to
the boundary realization surface.
-/
structure HilbertSourcePresentation where
  boundaryPresentation : BoundaryStreamPresentation
  hilbertSource : BoundaryHilbertSource
  hilbertSource_eq :
    hilbertSource =
      boundaryHilbertSource boundaryPresentation.packet
  gnsScalar : ℝ
  gnsScalar_eq :
    gnsScalar = boundaryHermitianGNSScalar hilbertSource

namespace HilbertSourcePresentation

/-- The completed boundary Hilbert source in the presentation. -/
def source (P : HilbertSourcePresentation) : BoundaryHilbertSource :=
  P.hilbertSource

/-- The Hermitian/GNS scalar in the presentation. -/
def scalar (P : HilbertSourcePresentation) : ℝ :=
  P.gnsScalar

end HilbertSourcePresentation

end AnalyticMotives
end LFunctions
end Boundary
