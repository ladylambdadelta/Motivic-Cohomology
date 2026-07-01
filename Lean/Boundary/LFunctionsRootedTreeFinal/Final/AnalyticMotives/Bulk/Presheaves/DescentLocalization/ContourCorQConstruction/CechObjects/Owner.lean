import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.ContourCorQConstruction.Covers.Owner

/-!
# Constructed Cech objects for contour descent

This owner records the Cech data associated to a constructed presheaf and one
conservative contour descent cover.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Cech data for a constructed `ContourCor_Q` presheaf descent cover. -/
structure ConstructedContourCechObject
    {F : ConstructedContourPresheafObject}
    (C : ConstructedContourPresheafDescentCover F) where
  pieceValue :
    (i : C.cover.CoverIndex) →
      ConstructedContourPresheafObject.valueAt F C.target
  gluedValue :
    ConstructedContourPresheafObject.valueAt F C.target

namespace ConstructedContourCechObject

/-- The value assigned to one cover piece. -/
def valueAtPiece {F : ConstructedContourPresheafObject}
    {C : ConstructedContourPresheafDescentCover F}
    (K : ConstructedContourCechObject C)
    (i : C.cover.CoverIndex) :
    ConstructedContourPresheafObject.valueAt F C.target :=
  K.pieceValue i

/-- The glued value selected by a constructed Cech object. -/
def glued {F : ConstructedContourPresheafObject}
    {C : ConstructedContourPresheafDescentCover F}
    (K : ConstructedContourCechObject C) :
    ConstructedContourPresheafObject.valueAt F C.target :=
  K.gluedValue

/-- The target bulk of the descent cover generating a constructed Cech object. -/
def targetBulk {F : ConstructedContourPresheafObject}
    {C : ConstructedContourPresheafDescentCover F}
    (K : ConstructedContourCechObject C) :
    ContourAdmissibleBulk :=
  C.target

end ConstructedContourCechObject

end AnalyticMotives
end LFunctions
end Boundary
