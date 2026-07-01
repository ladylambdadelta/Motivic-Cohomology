import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ResidueLedger.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.Owner

/-!
# Residue-pushforward commutation

This file owns the statement that contour pushforward along a correspondence
commutes with boundary residue maps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Residue-pushforward commutation for one source contour stage and one source
boundary face.  It compares the source residue span with the target residue
span after applying contour-chain and boundary-stratum transport.
-/
structure AnalyticResidueCommutation
    {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    {T : AnalyticContourTransport S}
    (s : X.contour.exhaustion.Stage)
    (i : X.boundary.FaceIndex) where
  residueCoreMap :
    AnalyticBulkCoreHom
      (X.residue.residue s i).residueCore
      (Y.residue.residue (T.pushforward.stageMap s) (T.boundary.faceMap i)).residueCore
  contour_commutes :
    AnalyticBulkCoreHom.comp
      (X.residue.residue s i).toContourDomain
      (T.pushforward.chainMap s) =
    AnalyticBulkCoreHom.comp
      residueCoreMap
      (Y.residue.residue (T.pushforward.stageMap s) (T.boundary.faceMap i)).toContourDomain
  face_commutes :
    AnalyticBulkCoreHom.comp
      (X.residue.residue s i).toFaceStratum
      (T.boundary.faceStratumMap i) =
    AnalyticBulkCoreHom.comp
      residueCoreMap
      (Y.residue.residue (T.pushforward.stageMap s) (T.boundary.faceMap i)).toFaceStratum

namespace AnalyticResidueCommutation

/-- The map between residue cores carried by residue commutation data. -/
def map {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    {T : AnalyticContourTransport S}
    {s : X.contour.exhaustion.Stage}
    {i : X.boundary.FaceIndex}
    (R : AnalyticResidueCommutation s i) :
    AnalyticBulkCoreHom
      (X.residue.residue s i).residueCore
      (Y.residue.residue (T.pushforward.stageMap s) (T.boundary.faceMap i)).residueCore :=
  R.residueCoreMap

/-- The contour-domain square in residue-pushforward commutation. -/
theorem contour_square {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    {T : AnalyticContourTransport S}
    {s : X.contour.exhaustion.Stage}
    {i : X.boundary.FaceIndex}
    (R : AnalyticResidueCommutation s i) :
    AnalyticBulkCoreHom.comp
      (X.residue.residue s i).toContourDomain
      (T.pushforward.chainMap s) =
    AnalyticBulkCoreHom.comp
      R.residueCoreMap
      (Y.residue.residue (T.pushforward.stageMap s) (T.boundary.faceMap i)).toContourDomain :=
  R.contour_commutes

/-- The boundary-stratum square in residue-pushforward commutation. -/
theorem face_square {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    {T : AnalyticContourTransport S}
    {s : X.contour.exhaustion.Stage}
    {i : X.boundary.FaceIndex}
    (R : AnalyticResidueCommutation s i) :
    AnalyticBulkCoreHom.comp
      (X.residue.residue s i).toFaceStratum
      (T.boundary.faceStratumMap i) =
    AnalyticBulkCoreHom.comp
      R.residueCoreMap
      (Y.residue.residue (T.pushforward.stageMap s) (T.boundary.faceMap i)).toFaceStratum :=
  R.face_commutes

end AnalyticResidueCommutation

end AnalyticMotives
end LFunctions
end Boundary
