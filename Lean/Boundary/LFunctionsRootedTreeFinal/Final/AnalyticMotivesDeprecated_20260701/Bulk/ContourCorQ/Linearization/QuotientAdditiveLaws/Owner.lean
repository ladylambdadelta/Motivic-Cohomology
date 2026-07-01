import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.AdditiveReindexing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.QuotientOperations.Owner

/-!
# Additive laws for quotient rational contour sums

This owner turns additive reindexing witnesses for finite formal sums into
equalities of quotient homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Quotient addition is commutative. -/
theorem addClass_comm {X Y : ContourCorQObject}
    (A B : QuotientHom X Y) :
    addClass A B = addClass B A :=
  Quotient.inductionOn A
    (fun S =>
      Quotient.inductionOn B
        (fun T =>
          Eq.trans
            (addClass_quotientClass S T)
            (Eq.trans
              (Quotient.sound
                (Nonempty.intro
                  (ContourCorQFormalSumReindexing.add_comm S T)))
              (Eq.symm (addClass_quotientClass T S)))))

/-- Quotient addition is associative. -/
theorem addClass_assoc {X Y : ContourCorQObject}
    (A B C : QuotientHom X Y) :
    addClass (addClass A B) C =
      addClass A (addClass B C) :=
  Quotient.inductionOn A
    (fun S =>
      Quotient.inductionOn B
        (fun T =>
          Quotient.inductionOn C
            (fun U =>
              Eq.trans
                (congrArg
                  (fun V => addClass V (quotientClass U))
                  (addClass_quotientClass S T))
                (Eq.trans
                  (addClass_quotientClass
                    (ContourCorQFormalSum.add S T) U)
                  (Eq.trans
                    (Quotient.sound
                      (Nonempty.intro
                        (ContourCorQFormalSumReindexing.add_assoc S T U)))
                    (Eq.trans
                      (Eq.symm
                        (addClass_quotientClass
                          S (ContourCorQFormalSum.add T U)))
                      (Eq.symm
                        (congrArg
                          (fun V => addClass (quotientClass S) V)
                          (addClass_quotientClass T U))))))))

/-- The empty formal sum is a left identity for quotient addition. -/
theorem zeroClass_addClass {X Y : ContourCorQObject}
    (A : QuotientHom X Y) :
    addClass (zeroClass X Y) A = A :=
  Quotient.inductionOn A
    (fun S =>
      Eq.trans
        (addClass_quotientClass (ContourCorQFormalSum.zero X Y) S)
        (Quotient.sound
          (Nonempty.intro
            (ContourCorQFormalSumReindexing.zero_add S))))

/-- The empty formal sum is a right identity for quotient addition. -/
theorem addClass_zeroClass {X Y : ContourCorQObject}
    (A : QuotientHom X Y) :
    addClass A (zeroClass X Y) = A :=
  Quotient.inductionOn A
    (fun S =>
      Eq.trans
        (addClass_quotientClass S (ContourCorQFormalSum.zero X Y))
        (Quotient.sound
          (Nonempty.intro
            (ContourCorQFormalSumReindexing.add_zero S))))

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary
