import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Core.Owner

/-!
# Morphisms of `ContourCor_Q`

This owner fixes the unlinearized morphism side: contour-compatible analytic
correspondences between contour-admissible analytic bulks.  Identity and
composition belong downstream, after constructed support/refinement/transport
and residue compatibility.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Unlinearized contour-correspondence homs. -/
abbrev ContourCorQRawHom
    (X Y : ContourCorQObject) :=
  ContourAnalyticCorrespondence X Y

end AnalyticMotives
end LFunctions
end Boundary
