import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Homs.Owner

/-!
# Rational linearization for `ContourCor_Q`

This owner contains the rational finite-sum hom data of `ContourCor_Q`.
Identity and composition for these sums belong downstream, after the
underlying contour-correspondence identity and composition are constructed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A finite formal rational sum of raw contour correspondences from `X` to `Y`.
The finite index type records the summands without asking for decidable
equality on raw contour correspondences.
-/
structure ContourCorQFormalSum
    (X Y : ContourCorQObject) where
  Index : Type
  finiteIndex : Finite Index
  coefficient : Index → Rat
  correspondence : Index → ContourCorQRawHom X Y

namespace ContourCorQFormalSum

/-- The summand index type of a finite rational contour sum. -/
def index {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) : Type :=
  S.Index

/-- The rational coefficient at a summand. -/
def coeffAt {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) (i : S.Index) : Rat :=
  S.coefficient i

/-- The raw contour correspondence at a summand. -/
def correspondenceAt {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) (i : S.Index) :
    ContourCorQRawHom X Y :=
  S.correspondence i

/-- A one-term formal sum with a chosen rational coefficient. -/
def term {X Y : ContourCorQObject}
    (q : Rat) (f : ContourCorQRawHom X Y) :
    ContourCorQFormalSum X Y where
  Index := PUnit
  finiteIndex := inferInstance
  coefficient := fun _ => q
  correspondence := fun _ => f

/-- A one-term formal sum with coefficient `1`. -/
def single {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    ContourCorQFormalSum X Y :=
  term 1 f

/-- The empty formal sum. -/
def zero (X Y : ContourCorQObject) :
    ContourCorQFormalSum X Y where
  Index := Empty
  finiteIndex := inferInstance
  coefficient := fun i => nomatch i
  correspondence := fun i => nomatch i

/-- Scale all coefficients in a finite formal sum by a rational number. -/
def scale {X Y : ContourCorQObject}
    (q : Rat) (S : ContourCorQFormalSum X Y) :
    ContourCorQFormalSum X Y where
  Index := S.Index
  finiteIndex := S.finiteIndex
  coefficient := fun i => q * S.coefficient i
  correspondence := S.correspondence

/-- Add two finite formal sums by disjoint union of their summand indices. -/
def add {X Y : ContourCorQObject}
    (S T : ContourCorQFormalSum X Y) :
    ContourCorQFormalSum X Y where
  Index := Sum S.Index T.Index
  finiteIndex := inferInstance
  coefficient :=
    Sum.elim S.coefficient T.coefficient
  correspondence :=
    Sum.elim S.correspondence T.correspondence

/-- Negate a finite formal sum by scaling all coefficients by `-1`. -/
def neg {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    ContourCorQFormalSum X Y :=
  scale (-1) S

/-- Subtract finite formal sums by adding the negation. -/
def sub {X Y : ContourCorQObject}
    (S T : ContourCorQFormalSum X Y) :
    ContourCorQFormalSum X Y :=
  add S (neg T)

end ContourCorQFormalSum

/-- Rationally linearized hom data before identities and composition are installed. -/
abbrev ContourCorQLinearHom
    (X Y : ContourCorQObject) :=
  ContourCorQFormalSum X Y

end AnalyticMotives
end LFunctions
end Boundary
