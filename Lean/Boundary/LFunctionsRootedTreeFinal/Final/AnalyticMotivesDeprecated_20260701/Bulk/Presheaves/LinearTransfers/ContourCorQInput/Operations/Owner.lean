import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Homs.Owner

/-!
# Operations for the `ContourCor_Q` presheaf input

This owner exposes the rational additive operations on transfer-input homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero presheaf-input contour hom. -/
def ContourCorQPresheafHom.zero
    (X Y : ContourCorQPresheafObject) :
    ContourCorQPresheafHom X Y :=
  ContourCorQHom.zero X Y

/-- Addition of presheaf-input contour homs. -/
def ContourCorQPresheafHom.add
    {X Y : ContourCorQPresheafObject}
    (F G : ContourCorQPresheafHom X Y) :
    ContourCorQPresheafHom X Y :=
  ContourCorQHom.add F G

/-- Scalar multiplication of presheaf-input contour homs. -/
def ContourCorQPresheafHom.scale
    {X Y : ContourCorQPresheafObject}
    (q : Rat) (F : ContourCorQPresheafHom X Y) :
    ContourCorQPresheafHom X Y :=
  ContourCorQHom.scale q F

/-- Negation of presheaf-input contour homs. -/
def ContourCorQPresheafHom.neg
    {X Y : ContourCorQPresheafObject}
    (F : ContourCorQPresheafHom X Y) :
    ContourCorQPresheafHom X Y :=
  ContourCorQHom.neg F

/-- Subtraction of presheaf-input contour homs. -/
def ContourCorQPresheafHom.sub
    {X Y : ContourCorQPresheafObject}
    (F G : ContourCorQPresheafHom X Y) :
    ContourCorQPresheafHom X Y :=
  ContourCorQHom.sub F G

end AnalyticMotives
end LFunctions
end Boundary
