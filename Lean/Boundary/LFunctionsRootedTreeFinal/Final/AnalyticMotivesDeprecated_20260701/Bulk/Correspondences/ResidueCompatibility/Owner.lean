import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.ResidueCompatibility.Commutation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.ResidueCompatibility.CompositionStability.Owner

/-!
# Residue compatibility for analytic correspondences

Residue compatibility states that correspondence pushforward commutes with the
boundary residue maps owned by the residue-ledger layer.  This is the analytic
analogue of boundary/Gysin compatibility and is upstream of trace identities.

Dependency order: residue-pushforward commutation first, then stability under
composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Residue compatibility for contour transport along an analytic correspondence
support.  It supplies residue-pushforward commutation for every source contour
stage and every source boundary face.
-/
structure AnalyticResidueCompatibility
    {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S) where
  commutation :
    (s : X.contour.exhaustion.Stage) →
      (i : X.boundary.FaceIndex) →
        AnalyticResidueCommutation s i

namespace AnalyticResidueCompatibility

/-- The residue commutation datum at a source contour stage and boundary face. -/
def commutationAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    {T : AnalyticContourTransport S}
    (R : AnalyticResidueCompatibility T)
    (s : X.contour.exhaustion.Stage) (i : X.boundary.FaceIndex) :
    AnalyticResidueCommutation s i :=
  R.commutation s i

end AnalyticResidueCompatibility

end AnalyticMotives
end LFunctions
end Boundary
