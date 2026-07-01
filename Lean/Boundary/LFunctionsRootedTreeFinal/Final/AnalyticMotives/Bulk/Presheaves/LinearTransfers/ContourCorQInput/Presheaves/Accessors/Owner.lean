import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Pullback.Owner

/-!
# Presheaves on `ContourCor_Q`

This owner packages value and pullback data for presheaves on the balanced
rational contour-correspondence input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A presheaf on the balanced rational contour-correspondence input. -/
structure ContourCorQPresheaf where
  values : ContourCorQPresheafValues
  pullbacks : ContourCorQPresheafPullback values

namespace ContourCorQPresheaf

/-- The value assignment of a `ContourCor_Q` presheaf. -/
def valueData (F : ContourCorQPresheaf) :
    ContourCorQPresheafValues :=
  F.values

/-- The value of a `ContourCor_Q` presheaf on an object. -/
def valueAt (F : ContourCorQPresheaf)
    (X : ContourCorQPresheafObject) : Type :=
  F.values.valueAt X

/-- The pullback data of a `ContourCor_Q` presheaf. -/
def pullbackData (F : ContourCorQPresheaf) :
    ContourCorQPresheafPullback F.values :=
  F.pullbacks

/-- Pullback along a balanced rational contour transfer hom. -/
def pullbackAlong (F : ContourCorQPresheaf)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y) :
    F.valueAt Y → F.valueAt X :=
  F.pullbacks.along f

end ContourCorQPresheaf

end AnalyticMotives
end LFunctions
end Boundary
