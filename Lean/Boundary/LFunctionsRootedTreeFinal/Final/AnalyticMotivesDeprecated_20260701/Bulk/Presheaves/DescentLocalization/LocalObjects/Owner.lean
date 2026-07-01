import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.LocalEquivalences.Owner

/-!
# Descent local objects

This file owns descent-local presheaves with contour transfers.  Interval
localization is downstream from descent-local objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Descent-locality data for a presheaf with contour transfers.  For every
contour descent cover and Cech object, it records the local-equivalence datum
against which the presheaf is required to be local.
-/
structure ContourDescentLocalObject
    (F : AnalyticPresheafWithTransfers) where
  localEquivalence :
    (C : TransferPresheafDescentCover F) →
      (K : ContourCechObject C) →
        ContourDescentLocalEquivalence K

namespace ContourDescentLocalObject

/-- The local-equivalence datum selected for a cover and Cech object. -/
def localEquivalenceAt {F : AnalyticPresheafWithTransfers}
    (L : ContourDescentLocalObject F)
    (C : TransferPresheafDescentCover F)
    (K : ContourCechObject C) :
    ContourDescentLocalEquivalence K :=
  L.localEquivalence C K

/-- The target value selected by descent-locality for a cover and Cech object. -/
def targetValueAt {F : AnalyticPresheafWithTransfers}
    (L : ContourDescentLocalObject F)
    (C : TransferPresheafDescentCover F)
    (K : ContourCechObject C) :
    F.valueAt C.target :=
  (L.localEquivalenceAt C K).target

/-- The restriction value selected by descent-locality at a Cech piece. -/
def restrictionAt {F : AnalyticPresheafWithTransfers}
    (L : ContourDescentLocalObject F)
    (C : TransferPresheafDescentCover F)
    (K : ContourCechObject C)
    (i : K.PieceIndex) :
    F.valueAt (K.pieceBulk i) :=
  (L.localEquivalenceAt C K).restrictionAt i

end ContourDescentLocalObject

/--
Descent-locality data for a functorial presheaf with transfers.  The cover and
Cech calculus is inherited from the underlying lightweight presheaf, while the
functorial transfer laws remain part of the source object.
-/
structure FunctorialContourDescentLocalObject
    (F : FunctorialAnalyticPresheafWithTransfers) where
  localObject : ContourDescentLocalObject F.forget

namespace FunctorialContourDescentLocalObject

/-- The underlying descent-locality data for the forgotten presheaf. -/
def underlying {F : FunctorialAnalyticPresheafWithTransfers}
    (L : FunctorialContourDescentLocalObject F) :
    ContourDescentLocalObject F.forget :=
  L.localObject

/-- The local-equivalence datum selected for a functorial cover and Cech object. -/
def localEquivalenceAt {F : FunctorialAnalyticPresheafWithTransfers}
    (L : FunctorialContourDescentLocalObject F)
    (C : TransferPresheafDescentCover F.forget)
    (K : ContourCechObject C) :
    ContourDescentLocalEquivalence K :=
  L.localObject.localEquivalence C K

/-- The target value selected by functorial descent-locality. -/
def targetValueAt {F : FunctorialAnalyticPresheafWithTransfers}
    (L : FunctorialContourDescentLocalObject F)
    (C : TransferPresheafDescentCover F.forget)
    (K : ContourCechObject C) :
    F.forget.valueAt C.target :=
  (L.localEquivalenceAt C K).target

/-- The restriction value selected by functorial descent-locality at a Cech piece. -/
def restrictionAt {F : FunctorialAnalyticPresheafWithTransfers}
    (L : FunctorialContourDescentLocalObject F)
    (C : TransferPresheafDescentCover F.forget)
    (K : ContourCechObject C)
    (i : K.PieceIndex) :
    F.forget.valueAt (K.pieceBulk i) :=
  (L.localEquivalenceAt C K).restrictionAt i

end FunctorialContourDescentLocalObject

end AnalyticMotives
end LFunctions
end Boundary
