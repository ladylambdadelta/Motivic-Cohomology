import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.LinearPullback.Owner

/-!
# Linear presheaves on `ContourCor_Q`

This owner packages a presheaf on balanced rational contour transfer homs with
rational-linear value data and linearity of pullback maps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A rational-linear presheaf on the balanced `ContourCor_Q` transfer input. -/
structure ContourCorQLinearPresheaf where
  presheaf : ContourCorQPresheaf
  linearValues : ContourCorQPresheafLinearValues presheaf
  linearPullback : ContourCorQPresheafLinearPullback linearValues

namespace ContourCorQLinearPresheaf

/-- The underlying raw `ContourCor_Q` presheaf. -/
def underlying (F : ContourCorQLinearPresheaf) :
    ContourCorQPresheaf :=
  F.presheaf

/-- The value of a linear presheaf on an object. -/
def valueAt (F : ContourCorQLinearPresheaf)
    (X : ContourCorQPresheafObject) : Type :=
  F.presheaf.valueAt X

/-- Pullback along one transfer hom. -/
def pullbackAlong (F : ContourCorQLinearPresheaf)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y) :
    F.valueAt Y → F.valueAt X :=
  F.presheaf.pullbackAlong f

/-- The zero value at an object. -/
def zeroAt (F : ContourCorQLinearPresheaf)
    (X : ContourCorQPresheafObject) :
    F.valueAt X :=
  F.linearValues.zeroAt X

/-- Addition in one value. -/
def addAt (F : ContourCorQLinearPresheaf)
    (X : ContourCorQPresheafObject)
    (a b : F.valueAt X) :
    F.valueAt X :=
  F.linearValues.addAt X a b

/-- Pullback preserves addition in values. -/
theorem pullback_add_eq (F : ContourCorQLinearPresheaf)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y)
    (a b : F.valueAt Y) :
    F.pullbackAlong f (F.addAt Y a b) =
      F.addAt X (F.pullbackAlong f a) (F.pullbackAlong f b) :=
  ContourCorQPresheafLinearPullback.map_add_eq
    F.linearPullback f a b

/-- Pullback preserves zero values. -/
theorem pullback_zero_eq (F : ContourCorQLinearPresheaf)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y) :
    F.pullbackAlong f (F.zeroAt Y) = F.zeroAt X :=
  ContourCorQPresheafLinearPullback.map_zero_eq
    F.linearPullback f

end ContourCorQLinearPresheaf

end AnalyticMotives
end LFunctions
end Boundary
