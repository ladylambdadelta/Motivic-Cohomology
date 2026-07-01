import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Faces.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.DeformationCompatibility.Owner

/-!
# Boundary-face compatibility for contour transport

This file owns compatibility of contour transport with boundary faces.  Residue
compatibility is downstream from this boundary behavior.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Boundary-face compatibility for contour transport.  It records the target
boundary face associated to each source boundary face and transports incidence
data along that assignment.
-/
structure AnalyticTransportBoundaryCompatibility
    {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (P : AnalyticContourPushforward S) where
  faceMap : X.boundary.FaceIndex → Y.boundary.FaceIndex
  faceStratumMap :
    (i : X.boundary.FaceIndex) →
      AnalyticBulkCoreHom
        (X.boundary.face i).stratum
        (Y.boundary.face (faceMap i)).stratum
  incidenceMap :
    {lower upper : X.boundary.FaceIndex} →
      X.boundary.IncidenceIndex lower upper →
        Y.boundary.IncidenceIndex (faceMap lower) (faceMap upper)

namespace AnalyticTransportBoundaryCompatibility

/-- The target boundary face index assigned to a source boundary face index. -/
def faceAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    {P : AnalyticContourPushforward S}
    (B : AnalyticTransportBoundaryCompatibility P)
    (i : X.boundary.FaceIndex) : Y.boundary.FaceIndex :=
  B.faceMap i

/-- The target incidence index induced by a source incidence index. -/
def incidenceAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    {P : AnalyticContourPushforward S}
    (B : AnalyticTransportBoundaryCompatibility P)
    {lower upper : X.boundary.FaceIndex}
    (I : X.boundary.IncidenceIndex lower upper) :
    Y.boundary.IncidenceIndex (B.faceMap lower) (B.faceMap upper) :=
  B.incidenceMap I

/-- The map of boundary-face strata assigned to a source boundary face. -/
def faceStratumMapAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    {P : AnalyticContourPushforward S}
    (B : AnalyticTransportBoundaryCompatibility P)
    (i : X.boundary.FaceIndex) :
    AnalyticBulkCoreHom
      (X.boundary.face i).stratum
      (Y.boundary.face (B.faceMap i)).stratum :=
  B.faceStratumMap i

end AnalyticTransportBoundaryCompatibility

end AnalyticMotives
end LFunctions
end Boundary
