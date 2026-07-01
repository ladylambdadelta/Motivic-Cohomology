import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Equivalence.Owner

/-!
# Operations on quotient rational contour sums

This owner descends the elementary formal-sum operations through reindexing
equivalence.  It supplies the operation surface for quotient homs before any
identity, composition, or additive law package is installed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- The zero quotient hom represented by the empty formal sum. -/
def zeroClass (X Y : ContourCorQObject) :
    QuotientHom X Y :=
  quotientClass (ContourCorQFormalSum.zero X Y)

/-- The quotient hom represented by one raw contour correspondence. -/
def singleClass {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    QuotientHom X Y :=
  quotientClass (ContourCorQFormalSum.single f)

/-- Scalar multiplication on quotient homs. -/
def scaleClass {X Y : ContourCorQObject}
    (q : Rat) (A : QuotientHom X Y) :
    QuotientHom X Y :=
  Quotient.liftOn A
    (fun S => quotientClass (ContourCorQFormalSum.scale q S))
    (fun S T h =>
      Quotient.sound (reindexingRel_scale q h))

/-- Scalar multiplication reduces to coefficient scaling on representatives. -/
theorem scaleClass_quotientClass {X Y : ContourCorQObject}
    (q : Rat) (S : ContourCorQFormalSum X Y) :
    scaleClass q (quotientClass S) =
      quotientClass (ContourCorQFormalSum.scale q S) :=
  rfl

/-- Addition on quotient homs. -/
def addClass {X Y : ContourCorQObject}
    (A B : QuotientHom X Y) :
    QuotientHom X Y :=
  Quotient.liftOn A
    (fun S =>
      Quotient.liftOn B
        (fun T => quotientClass (ContourCorQFormalSum.add S T))
        (fun T U hTU =>
          Quotient.sound
            (reindexingRel_add (reindexingRel_refl S) hTU)))
    (fun S T hST =>
      Quotient.inductionOn B
        (fun U =>
          Quotient.sound
            (reindexingRel_add hST (reindexingRel_refl U))))

/-- Addition reduces to formal-sum addition on representatives. -/
theorem addClass_quotientClass {X Y : ContourCorQObject}
    (S T : ContourCorQFormalSum X Y) :
    addClass (quotientClass S) (quotientClass T) =
      quotientClass (ContourCorQFormalSum.add S T) :=
  rfl

/-- Negation on quotient homs. -/
def negClass {X Y : ContourCorQObject}
    (A : QuotientHom X Y) :
    QuotientHom X Y :=
  scaleClass (-1) A

/-- Negation reduces to formal-sum negation on representatives. -/
theorem negClass_quotientClass {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    negClass (quotientClass S) =
      quotientClass (ContourCorQFormalSum.neg S) :=
  rfl

/-- Subtraction on quotient homs. -/
def subClass {X Y : ContourCorQObject}
    (A B : QuotientHom X Y) :
    QuotientHom X Y :=
  addClass A (negClass B)

/-- Subtraction reduces to formal-sum subtraction on representatives. -/
theorem subClass_quotientClass {X Y : ContourCorQObject}
    (S T : ContourCorQFormalSum X Y) :
    subClass (quotientClass S) (quotientClass T) =
      quotientClass (ContourCorQFormalSum.sub S T) :=
  rfl

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary
