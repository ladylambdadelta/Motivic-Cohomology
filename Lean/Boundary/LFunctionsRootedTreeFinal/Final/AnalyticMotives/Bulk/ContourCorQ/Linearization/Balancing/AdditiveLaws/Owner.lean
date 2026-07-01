import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.AdditiveReindexing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Balancing.Operations.Owner

/-!
# Additive laws for balanced quotient homs

This owner proves the additive laws for the balanced quotient hom surface from
the explicit additive reindexing witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Balanced quotient addition is commutative. -/
theorem balancedAddClass_comm {X Y : ContourCorQObject}
    (A B : BalancedQuotientHom X Y) :
    balancedAddClass A B = balancedAddClass B A :=
  Quotient.inductionOn A
    (fun S =>
      Quotient.inductionOn B
        (fun T =>
          Eq.trans
            (balancedAddClass_balancedClass S T)
            (Eq.trans
              (Quotient.sound
                (balancedRel_of_reindexing
                  (Nonempty.intro
                    (ContourCorQFormalSumReindexing.add_comm S T))))
              (Eq.symm (balancedAddClass_balancedClass T S)))))

/-- Balanced quotient addition is associative. -/
theorem balancedAddClass_assoc {X Y : ContourCorQObject}
    (A B C : BalancedQuotientHom X Y) :
    balancedAddClass (balancedAddClass A B) C =
      balancedAddClass A (balancedAddClass B C) :=
  Quotient.inductionOn A
    (fun S =>
      Quotient.inductionOn B
        (fun T =>
          Quotient.inductionOn C
            (fun U =>
              Eq.trans
                (congrArg
                  (fun V => balancedAddClass V (balancedClass U))
                  (balancedAddClass_balancedClass S T))
                (Eq.trans
                  (balancedAddClass_balancedClass
                    (ContourCorQFormalSum.add S T) U)
                  (Eq.trans
                    (Quotient.sound
                      (balancedRel_of_reindexing
                        (Nonempty.intro
                          (ContourCorQFormalSumReindexing.add_assoc S T U))))
                    (Eq.trans
                      (Eq.symm
                        (balancedAddClass_balancedClass
                          S (ContourCorQFormalSum.add T U)))
                      (Eq.symm
                        (congrArg
                          (fun V => balancedAddClass (balancedClass S) V)
                          (balancedAddClass_balancedClass T U))))))))

/-- The balanced zero class is a left identity for addition. -/
theorem balancedZeroClass_addClass {X Y : ContourCorQObject}
    (A : BalancedQuotientHom X Y) :
    balancedAddClass (balancedZeroClass X Y) A = A :=
  Quotient.inductionOn A
    (fun S =>
      Eq.trans
        (balancedAddClass_balancedClass (ContourCorQFormalSum.zero X Y) S)
        (Quotient.sound
          (balancedRel_of_reindexing
            (Nonempty.intro
              (ContourCorQFormalSumReindexing.zero_add S)))))

/-- The balanced zero class is a right identity for addition. -/
theorem balancedAddClass_zeroClass {X Y : ContourCorQObject}
    (A : BalancedQuotientHom X Y) :
    balancedAddClass A (balancedZeroClass X Y) = A :=
  Quotient.inductionOn A
    (fun S =>
      Eq.trans
        (balancedAddClass_balancedClass S (ContourCorQFormalSum.zero X Y))
        (Quotient.sound
          (balancedRel_of_reindexing
            (Nonempty.intro
              (ContourCorQFormalSumReindexing.add_zero S)))))

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary
