import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Associativity.Reindexing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Quotient.Owner

/-!
# Associativity for quotient composition

This owner descends the formal associativity reindexing law to quotient homs
modulo finite reindexing.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Quotient composition is associative. -/
theorem compClass_assoc
    (C : ContourCorrespondenceCalculus)
    {W X Y Z : ContourCorQObject}
    (A : QuotientHom W X)
    (B : QuotientHom X Y)
    (D : QuotientHom Y Z) :
    compClass C (compClass C A B) D =
      compClass C A (compClass C B D) :=
  Quotient.inductionOn A
    (fun S =>
      Quotient.inductionOn B
        (fun T =>
          Quotient.inductionOn D
            (fun U =>
              Eq.trans
                (congrArg
                  (fun V => compClass C V (quotientClass U))
                  (compClass_quotientClass C S T))
                (Eq.trans
                  (compClass_quotientClass
                    C (ContourCorQFormalSum.comp C S T) U)
                  (Eq.trans
                    (Quotient.sound
                      (Nonempty.intro
                        (ContourCorQFormalSumReindexing.comp_assoc
                          C S T U)))
                    (Eq.trans
                      (Eq.symm
                        (compClass_quotientClass
                          C S (ContourCorQFormalSum.comp C T U)))
                      (Eq.symm
                        (congrArg
                          (fun V => compClass C (quotientClass S) V)
                          (compClass_quotientClass C T U)))))))))

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary
