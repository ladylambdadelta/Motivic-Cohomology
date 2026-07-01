import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.AdditiveReindexing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.AdditiveLaws.Owner

/-!
# Linear relations in balanced quotient homs

This owner exposes the first usable rational-linear consequences of the
balancing relation: zero coefficient terms vanish, and equal raw contour
correspondences collect their coefficients.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Appending a zero coefficient term does not change a balanced class. -/
theorem balancedAddClass_zeroTerm_right {X Y : ContourCorQObject}
    (A : BalancedQuotientHom X Y)
    (f : ContourCorQRawHom X Y) :
    balancedAddClass A (balancedTermClass 0 f) = A :=
  Quotient.inductionOn A
    (fun S =>
      Eq.trans
        (balancedAddClass_balancedClass S (ContourCorQFormalSum.term 0 f))
        (Quotient.sound
          (BalancedRel.elementary
            (ElementaryBalancedRel.zero_term S f))))

/-- Prepending a zero coefficient term does not change a balanced class. -/
theorem balancedAddClass_zeroTerm_left {X Y : ContourCorQObject}
    (A : BalancedQuotientHom X Y)
    (f : ContourCorQRawHom X Y) :
    balancedAddClass (balancedTermClass 0 f) A = A :=
  Eq.trans
    (balancedAddClass_comm (balancedTermClass 0 f) A)
    (balancedAddClass_zeroTerm_right A f)

/-- A zero coefficient term is the balanced zero class. -/
theorem balancedTermClass_zero_coeff {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    balancedTermClass 0 f = balancedZeroClass X Y :=
  Eq.trans
    (Eq.symm
      (balancedZeroClass_addClass (balancedTermClass 0 f)))
    (balancedAddClass_zeroTerm_right (balancedZeroClass X Y) f)

/-- Equal raw contour correspondences collect their rational coefficients. -/
theorem balancedTermClass_collect {X Y : ContourCorQObject}
    (q r : Rat) (f : ContourCorQRawHom X Y) :
    balancedAddClass (balancedTermClass q f) (balancedTermClass r f) =
      balancedTermClass (q + r) f :=
  Eq.trans
    (balancedAddClass_balancedClass
      (ContourCorQFormalSum.term q f)
      (ContourCorQFormalSum.term r f))
    (Quotient.sound
      (BalancedRel.elementary
        (ElementaryBalancedRel.collect_terms q r f)))

/-- Scaling a one-term representative scales its rational coefficient. -/
theorem balancedScaleClass_term {X Y : ContourCorQObject}
    (p q : Rat) (f : ContourCorQRawHom X Y) :
    balancedScaleClass p (balancedTermClass q f) =
      balancedTermClass (p * q) f :=
  rfl

/-- A single raw correspondence is the coefficient-one term class. -/
theorem balancedSingleClass_eq_term_one {X Y : ContourCorQObject}
    (f : ContourCorQRawHom X Y) :
    balancedSingleClass f = balancedTermClass 1 f :=
  rfl

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary
