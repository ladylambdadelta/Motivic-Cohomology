import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.Pushforward.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.DeformationCompatibility.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.BoundaryCompatibility.Owner

/-!
# Contour transport for analytic correspondences

Contour transport records how a correspondence pushes admissible contour data
from source bulk to target bulk, together with deformation compatibility.

Dependency order: contour pushforward, deformation compatibility, then
boundary-face compatibility.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Contour transport data for an analytic correspondence support.  It combines
stage pushforward with compatibility for deformations and boundary-face
incidence.
-/
structure AnalyticContourTransport {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) where
  pushforward : AnalyticContourPushforward S
  deformation :
    AnalyticTransportDeformationCompatibility pushforward
  boundary :
    AnalyticTransportBoundaryCompatibility pushforward

namespace AnalyticContourTransport

/-- The contour-stage pushforward carried by transport data. -/
def pushforwardData {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S) : AnalyticContourPushforward S :=
  T.pushforward

/-- The deformation compatibility carried by transport data. -/
def deformationData {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S) :
    AnalyticTransportDeformationCompatibility T.pushforward :=
  T.deformation

/-- The boundary-face compatibility carried by transport data. -/
def boundaryData {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S) :
    AnalyticTransportBoundaryCompatibility T.pushforward :=
  T.boundary

/-- The image of a source contour stage under transport data. -/
def stageAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S)
    (s : X.contour.exhaustion.Stage) : Y.contour.exhaustion.Stage :=
  T.pushforward.stageMap s

/-- The target contour chain assigned to a source contour stage by transport data. -/
def chainAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S)
    (s : X.contour.exhaustion.Stage) :
    AnalyticContourChain Y.boundary :=
  T.pushforward.chainAt s

/-- The map of contour-chain domains assigned to a source contour stage. -/
def chainMapAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S)
    (s : X.contour.exhaustion.Stage) :
    AnalyticBulkCoreHom
      (X.contour.exhaustion.chain s).domain
      (Y.contour.exhaustion.chain (T.stageAt s)).domain :=
  T.pushforward.chainMapAt s

/-- The target boundary face assigned to a source boundary face by transport data. -/
def faceAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S)
    (i : X.boundary.FaceIndex) : Y.boundary.FaceIndex :=
  T.boundary.faceAt i

/-- The map of boundary-face strata assigned to a source boundary face. -/
def faceStratumMapAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S)
    (i : X.boundary.FaceIndex) :
    AnalyticBulkCoreHom
      (X.boundary.face i).stratum
      (Y.boundary.face (T.faceAt i)).stratum :=
  T.boundary.faceStratumMapAt i

/-- The target incidence index induced by a source incidence index. -/
def incidenceAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (T : AnalyticContourTransport S)
    {lower upper : X.boundary.FaceIndex}
    (I : X.boundary.IncidenceIndex lower upper) :
    Y.boundary.IncidenceIndex (T.faceAt lower) (T.faceAt upper) :=
  T.boundary.incidenceAt I

end AnalyticContourTransport

end AnalyticMotives
end LFunctions
end Boundary
