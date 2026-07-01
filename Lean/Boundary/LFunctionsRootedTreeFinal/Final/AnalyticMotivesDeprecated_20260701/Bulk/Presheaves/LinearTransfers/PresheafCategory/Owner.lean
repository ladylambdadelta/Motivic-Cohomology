import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.QLinearization.Owner

/-!
# Presheaf category on contour transfers

This file owns the presheaf category on the `ℚ`-linearized contour
correspondence category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A presheaf on the rational contour-correspondence graph.  It is contravariant:
a rational contour correspondence from `X` to `Y` acts by pullback from the
value at `Y` to the value at `X`.
-/
structure RationalContourPresheaf where
  value : ContourCorrespondenceObject → Type
  pullback :
    {X Y : ContourCorrespondenceObject} →
      RationalContourHom X Y → value Y → value X

namespace RationalContourPresheaf

/-- The value of a rational contour presheaf on a contour-admissible bulk. -/
def valueAt (F : RationalContourPresheaf)
    (X : ContourCorrespondenceObject) : Type :=
  F.value X

/-- Pullback along a rational contour correspondence. -/
def pullbackAlong (F : RationalContourPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    F.value Y → F.value X :=
  F.pullback f

end RationalContourPresheaf

end AnalyticMotives
end LFunctions
end Boundary
