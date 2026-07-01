import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.Quotient.Owner

/-!
# Operations on balanced quotient homs

This owner descends the formal finite-sum operations to the balanced quotient
hom type, the intended rational linear-span hom surface for `ContourCor_Q`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- The zero balanced quotient hom. -/
def balancedZeroClass (X Y : ContourCorQObject) :
    BalancedQuotientHom X Y :=
  balancedClass (ContourCorQFormalSum.zero X Y)

/-- The balanced class represented by one raw contour correspondence. -/
def balancedSingleClass {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    BalancedQuotientHom X Y :=
  balancedClass (ContourCorQFormalSum.single f)

/-- The balanced class represented by one rationally weighted raw correspondence. -/
def balancedTermClass {X Y : ContourCorQObject}
    (q : Rat) (f : ContourCorQRawHom X Y) :
    BalancedQuotientHom X Y :=
  balancedClass (ContourCorQFormalSum.term q f)

/-- Scalar multiplication on balanced quotient homs. -/
def balancedScaleClass {X Y : ContourCorQObject}
    (q : Rat) (A : BalancedQuotientHom X Y) :
    BalancedQuotientHom X Y :=
  Quotient.liftOn A
    (fun S => balancedClass (ContourCorQFormalSum.scale q S))
    (fun S T h =>
      Quotient.sound (BalancedRel.scale q h))

/-- Scalar multiplication reduces to formal scaling on representatives. -/
theorem balancedScaleClass_balancedClass {X Y : ContourCorQObject}
    (q : Rat) (S : ContourCorQFormalSum X Y) :
    balancedScaleClass q (balancedClass S) =
      balancedClass (ContourCorQFormalSum.scale q S) :=
  rfl

/-- Addition on balanced quotient homs. -/
def balancedAddClass {X Y : ContourCorQObject}
    (A B : BalancedQuotientHom X Y) :
    BalancedQuotientHom X Y :=
  Quotient.liftOn A
    (fun S =>
      Quotient.liftOn B
        (fun T => balancedClass (ContourCorQFormalSum.add S T))
        (fun T U hTU =>
          Quotient.sound
            (BalancedRel.add (BalancedRel.refl S) hTU)))
    (fun S T hST =>
      Quotient.inductionOn B
        (fun U =>
          Quotient.sound
            (BalancedRel.add hST (BalancedRel.refl U))))

/-- Addition reduces to formal addition on representatives. -/
theorem balancedAddClass_balancedClass {X Y : ContourCorQObject}
    (S T : ContourCorQFormalSum X Y) :
    balancedAddClass (balancedClass S) (balancedClass T) =
      balancedClass (ContourCorQFormalSum.add S T) :=
  rfl

/-- Negation on balanced quotient homs. -/
def balancedNegClass {X Y : ContourCorQObject}
    (A : BalancedQuotientHom X Y) :
    BalancedQuotientHom X Y :=
  balancedScaleClass (-1) A

/-- Negation reduces to formal negation on representatives. -/
theorem balancedNegClass_balancedClass {X Y : ContourCorQObject}
    (S : ContourCorQFormalSum X Y) :
    balancedNegClass (balancedClass S) =
      balancedClass (ContourCorQFormalSum.neg S) :=
  rfl

/-- Subtraction on balanced quotient homs. -/
def balancedSubClass {X Y : ContourCorQObject}
    (A B : BalancedQuotientHom X Y) :
    BalancedQuotientHom X Y :=
  balancedAddClass A (balancedNegClass B)

/-- Subtraction reduces to formal subtraction on representatives. -/
theorem balancedSubClass_balancedClass {X Y : ContourCorQObject}
    (S T : ContourCorQFormalSum X Y) :
    balancedSubClass (balancedClass S) (balancedClass T) =
      balancedClass (ContourCorQFormalSum.sub S T) :=
  rfl

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary
