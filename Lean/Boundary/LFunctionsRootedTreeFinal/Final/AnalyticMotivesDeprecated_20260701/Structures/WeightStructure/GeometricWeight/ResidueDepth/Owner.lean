import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ResidueLedger.Filtration.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.GeometricWeight.Strata.Owner

/-!
# Residue-depth input for geometric weights

This file owns the residue-depth filtration used by geometric-contour weights.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Residue-depth data for a geometric-weight stratum.  The depth is read from a
residue filtration on the underlying bulk boundary system.
-/
structure GeometricResidueDepth
    {S : AnalyticMotivicStableInfinityInterface}
    (W : GeometricWeightStratum S) where
  filtration : AnalyticResidueFiltration W.bulk.boundary
  depthValue : Nat
  depth_eq :
    depthValue = filtration.depth W.faceIndex

namespace GeometricResidueDepth

/-- The residue depth assigned to a geometric-weight stratum. -/
def depth {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightStratum S}
    (D : GeometricResidueDepth W) : Nat :=
  D.depthValue

/-- The defining equation relating assigned depth to the residue filtration. -/
theorem depth_eq_filtration {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightStratum S}
    (D : GeometricResidueDepth W) :
    D.depthValue = D.filtration.depth W.faceIndex :=
  D.depth_eq

end GeometricResidueDepth

end AnalyticMotives
end LFunctions
end Boundary
