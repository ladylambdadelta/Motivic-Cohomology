import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.TransferReady.Homs.Owner

/-!
# Transfer-ready hom laws for `ContourCor_Q`

This owner exposes the additive and rational-term laws for transfer-ready
hom names.  The proofs are wrappers over the balanced quotient layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Transfer-ready hom addition is commutative. -/
theorem ContourCorQHom.add_comm {X Y : ContourCorQObject}
    (F G : ContourCorQHom X Y) :
    ContourCorQHom.add F G = ContourCorQHom.add G F :=
  ContourCorQFormalSum.balancedAddClass_comm F G

/-- Transfer-ready hom addition is associative. -/
theorem ContourCorQHom.add_assoc {X Y : ContourCorQObject}
    (F G H : ContourCorQHom X Y) :
    ContourCorQHom.add (ContourCorQHom.add F G) H =
      ContourCorQHom.add F (ContourCorQHom.add G H) :=
  ContourCorQFormalSum.balancedAddClass_assoc F G H

/-- The zero transfer-ready hom is a left identity for addition. -/
theorem ContourCorQHom.zero_add {X Y : ContourCorQObject}
    (F : ContourCorQHom X Y) :
    ContourCorQHom.add (ContourCorQHom.zero X Y) F = F :=
  ContourCorQFormalSum.balancedZeroClass_addClass F

/-- The zero transfer-ready hom is a right identity for addition. -/
theorem ContourCorQHom.add_zero {X Y : ContourCorQObject}
    (F : ContourCorQHom X Y) :
    ContourCorQHom.add F (ContourCorQHom.zero X Y) = F :=
  ContourCorQFormalSum.balancedAddClass_zeroClass F

/-- A zero coefficient transfer-ready term is the zero hom. -/
theorem ContourCorQHom.term_zero_coeff {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    ContourCorQHom.term 0 f = ContourCorQHom.zero X Y :=
  ContourCorQFormalSum.balancedTermClass_zero_coeff f

/-- Adding a zero coefficient term on the right does not change a hom. -/
theorem ContourCorQHom.add_zero_term_right {X Y : ContourCorQObject}
    (F : ContourCorQHom X Y)
    (f : ContourCorQRawHom X Y) :
    ContourCorQHom.add F (ContourCorQHom.term 0 f) = F :=
  ContourCorQFormalSum.balancedAddClass_zeroTerm_right F f

/-- Adding a zero coefficient term on the left does not change a hom. -/
theorem ContourCorQHom.add_zero_term_left {X Y : ContourCorQObject}
    (F : ContourCorQHom X Y)
    (f : ContourCorQRawHom X Y) :
    ContourCorQHom.add (ContourCorQHom.term 0 f) F = F :=
  ContourCorQFormalSum.balancedAddClass_zeroTerm_left F f

/-- Equal raw correspondences collect coefficients in transfer-ready homs. -/
theorem ContourCorQHom.term_collect {X Y : ContourCorQObject}
    (q r : Rat) (f : ContourCorQRawHom X Y) :
    ContourCorQHom.add (ContourCorQHom.term q f) (ContourCorQHom.term r f) =
      ContourCorQHom.term (q + r) f :=
  ContourCorQFormalSum.balancedTermClass_collect q r f

/-- Scaling a one-term transfer-ready hom scales its rational coefficient. -/
theorem ContourCorQHom.scale_term {X Y : ContourCorQObject}
    (p q : Rat) (f : ContourCorQRawHom X Y) :
    ContourCorQHom.scale p (ContourCorQHom.term q f) =
      ContourCorQHom.term (p * q) f :=
  ContourCorQFormalSum.balancedScaleClass_term p q f

/-- A single raw correspondence is the coefficient-one transfer-ready term. -/
theorem ContourCorQHom.single_eq_term_one {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    ContourCorQHom.single f = ContourCorQHom.term 1 f :=
  ContourCorQFormalSum.balancedSingleClass_eq_term_one f

end AnalyticMotives
end LFunctions
end Boundary
