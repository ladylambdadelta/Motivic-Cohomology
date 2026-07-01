import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.ContourCorQConstruction.LocalEquivalences.Owner

/-!
# Constructed descent-local presheaves

This owner records descent-locality for constructed `ContourCor_Q` linear
presheaves.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-locality data for a constructed `ContourCor_Q` linear presheaf. -/
structure ConstructedContourDescentLocalObject
    (F : ConstructedContourPresheafObject) where
  localEquivalence :
    (C : ConstructedContourPresheafDescentCover F) →
      (K : ConstructedContourCechObject C) →
        ConstructedContourDescentLocalEquivalence K

namespace ConstructedContourDescentLocalObject

/-- The local-equivalence datum selected for one cover and Cech object. -/
def equivalenceAt {F : ConstructedContourPresheafObject}
    (L : ConstructedContourDescentLocalObject F)
    (C : ConstructedContourPresheafDescentCover F)
    (K : ConstructedContourCechObject C) :
    ConstructedContourDescentLocalEquivalence K :=
  L.localEquivalence C K

/-- The target value selected by descent-locality. -/
def targetAt {F : ConstructedContourPresheafObject}
    (L : ConstructedContourDescentLocalObject F)
    (C : ConstructedContourPresheafDescentCover F)
    (K : ConstructedContourCechObject C) :
    ConstructedContourPresheafObject.valueAt F C.target :=
  (L.equivalenceAt C K).target

/-- The selected target value agrees with the glued Cech value. -/
theorem target_eq_glued {F : ConstructedContourPresheafObject}
    (L : ConstructedContourDescentLocalObject F)
    (C : ConstructedContourPresheafDescentCover F)
    (K : ConstructedContourCechObject C) :
    L.targetAt C K = K.glued :=
  ConstructedContourDescentLocalEquivalence.target_eq_glued_value
    (L.equivalenceAt C K)

end ConstructedContourDescentLocalObject

/-- A constructed linear presheaf equipped with contour descent-locality. -/
structure ConstructedDescentLocalAnalyticPresheaf where
  presheaf : ConstructedContourPresheafObject
  descentLocality : ConstructedContourDescentLocalObject presheaf

namespace ConstructedDescentLocalAnalyticPresheaf

/-- The underlying constructed linear presheaf. -/
def underlying (F : ConstructedDescentLocalAnalyticPresheaf) :
    ConstructedContourPresheafObject :=
  F.presheaf

/-- The descent-locality data carried by the constructed presheaf. -/
def locality (F : ConstructedDescentLocalAnalyticPresheaf) :
    ConstructedContourDescentLocalObject F.presheaf :=
  F.descentLocality

end ConstructedDescentLocalAnalyticPresheaf

end AnalyticMotives
end LFunctions
end Boundary
