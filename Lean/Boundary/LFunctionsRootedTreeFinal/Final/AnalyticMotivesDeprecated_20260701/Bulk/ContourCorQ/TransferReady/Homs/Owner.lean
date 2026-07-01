import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.Owner

/-!
# Transfer-ready homs for `ContourCor_Q`

This owner gives the hom type consumed by presheaves with transfers: the
balanced rational linear span of raw contour-compatible analytic
correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Transfer-ready rational contour-correspondence homs. -/
abbrev ContourCorQHom
    (X Y : ContourCorQObject) : Type :=
  ContourCorQFormalSum.BalancedQuotientHom X Y

/-- The zero transfer-ready rational contour-correspondence hom. -/
def ContourCorQHom.zero
    (X Y : ContourCorQObject) :
    ContourCorQHom X Y :=
  ContourCorQFormalSum.balancedZeroClass X Y

/-- The transfer-ready class of one raw contour-compatible correspondence. -/
def ContourCorQHom.single {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    ContourCorQHom X Y :=
  ContourCorQFormalSum.balancedSingleClass f

/-- The transfer-ready class of one rationally weighted raw correspondence. -/
def ContourCorQHom.term {X Y : ContourCorQObject}
    (q : Rat) (f : ContourCorQRawHom X Y) :
    ContourCorQHom X Y :=
  ContourCorQFormalSum.balancedTermClass q f

/-- Addition of transfer-ready rational contour-correspondence homs. -/
def ContourCorQHom.add {X Y : ContourCorQObject}
    (F G : ContourCorQHom X Y) :
    ContourCorQHom X Y :=
  ContourCorQFormalSum.balancedAddClass F G

/-- Scalar multiplication of transfer-ready rational contour-correspondence homs. -/
def ContourCorQHom.scale {X Y : ContourCorQObject}
    (q : Rat) (F : ContourCorQHom X Y) :
    ContourCorQHom X Y :=
  ContourCorQFormalSum.balancedScaleClass q F

/-- Negation of transfer-ready rational contour-correspondence homs. -/
def ContourCorQHom.neg {X Y : ContourCorQObject}
    (F : ContourCorQHom X Y) :
    ContourCorQHom X Y :=
  ContourCorQFormalSum.balancedNegClass F

/-- Subtraction of transfer-ready rational contour-correspondence homs. -/
def ContourCorQHom.sub {X Y : ContourCorQObject}
    (F G : ContourCorQHom X Y) :
    ContourCorQHom X Y :=
  ContourCorQFormalSum.balancedSubClass F G

end AnalyticMotives
end LFunctions
end Boundary
